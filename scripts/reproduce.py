"""Replay unchanged V3 verifiers in a disposable directory; fail on mismatches."""
from pathlib import Path
from decimal import Decimal
import argparse
import importlib.metadata
import json
import math
import platform
import subprocess
import sys
import tempfile
import time
from staging_common import (ROOT, require, digest, load, save, verify_repo, unpack,
                            materialize, byte_manifest, output_directory, child_environment)

JOBS = [
    ('exact','current','scripts/clean_room_1r_search.py','results/clean_room_1r_search.json'),
    ('exact','current','scripts/verify_1r.py','results/target1r_exact.json'),
    ('exact','current','scripts/derive_short_time.py','results/short_time_symmetric.json'),
    ('exact','current','scripts/verify_target2_exact.py','results/target2_exact.json'),
    ('exact','current','scripts/verify_restricted_survivors.py','results/restricted_survivors.json'),
    ('legacy_mixed_exact_and_numerical','left','verify.py','verification_results.json'),
    ('legacy_mixed_exact_and_numerical','current','scripts/verify_1r_bootstrap.py','results/target1r_bootstrap.json'),
    ('legacy_mixed_exact_and_numerical','current','scripts/verify_factor_two.py','results/factor_two_verification.json'),
    ('numerical_nonrigorous','current','scripts/verify_target2_numerical.py','results/target2_numerical.json'),
]


def same(expected, observed, path='root'):
    # Preserve the original second-run comparison policy for JSON float fields.
    if isinstance(expected,dict):
        require(isinstance(observed,dict) and expected.keys()==observed.keys(), 'Structure mismatch: '+path)
        for key in expected:
            same(expected[key],observed[key],path+'.'+key)
    elif isinstance(expected,list):
        require(isinstance(observed,list) and len(expected)==len(observed), 'Length mismatch: '+path)
        for i,(a,b) in enumerate(zip(expected,observed)):
            same(a,b,f'{path}[{i}]')
    elif '.high_precision_90_digits.' in path:
        # These explicitly numerical strings are diagnostics, not exact rationals.
        a,b = Decimal(expected),Decimal(observed)
        require(a.is_finite() and b.is_finite() and abs(a-b)<=Decimal('1e-75'), 'High-precision mismatch: '+path)
        if path.endswith('_absolute_error'):
            require(abs(b)<Decimal('1e-75'), 'High-precision error bound failed: '+path)
    elif isinstance(expected,float):
        require(isinstance(observed,(int,float)) and not isinstance(observed,bool)
                and math.isfinite(observed) and math.isclose(expected,observed,rel_tol=1e-9,abs_tol=1e-9),
                f'Numerical mismatch: {path}: {expected!r} != {observed!r}')
    else:
        require(type(expected) is type(observed) and expected==observed,
                f'Exact mismatch: {path}: {expected!r} != {observed!r}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-assets',help='Optional private sibling asset directory; uses original mathematical ZIPs')
    parser.add_argument('--output',help='New output directory; defaults to .local/reproduction-TIMESTAMP')
    parser.add_argument('--timeout',type=int,default=1800,help='Seconds allowed per frozen verifier')
    args = parser.parse_args()
    require(not sys.flags.optimize, 'Run without -O; frozen verifier assertions must remain enabled')
    out = output_directory(args.output,'reproduction',args.private_assets)
    report = {'status':'FAIL','mode':'original_private_archives' if args.private_assets else 'public_curated_view',
              'scientific_authority':'V3 aaebb0e5b0768746bbd0c1eccb1fd128534680c54c8377de90e0c58365c29401',
              'python':platform.python_version(),'platform':platform.platform(),'jobs':[],
              'exact_comparison':'Strings, integers, booleans and structures identical.',
              'numerical_comparison':'Float fields abs/rel 1e-9, inherited from frozen second-run replay; explicit 90-digit diagnostic strings abs 1e-75. Frozen internal tolerances also run.',
              'scope':'Engineering replay of supplied evidence. Numerical cross-checks are non-rigorous; no new claim, hostile audit, clean-room run or human validation.'}
    lines=[]
    def log(message):
        lines.append(message); print(message,flush=True)
    try:
        report['integrity_before'] = verify_repo(args.private_assets)
        report['dependencies'] = {n:importlib.metadata.version(n) for n in ['numpy','scipy','sympy','mpmath']}
        pins = dict(line.split('==') for line in (ROOT/'requirements.txt').read_text().splitlines() if line.strip())
        require(report['dependencies']==pins,'Install the frozen versions from requirements.txt')
        log('Asset hashes and byte-identical views: PASS')
        if args.private_assets:
            private=Path(args.private_assets).resolve()
            current=unpack((private/'Krylov_remaining_attack_FINAL.zip').read_bytes(),strip_root=True)
            left=unpack((private/'P2_3_Krylov_exact_certificate.zip').read_bytes(),strip_root=True)
            report['nested_manifest_counts']={
                'current':byte_manifest(current,'MANIFEST.sha256'),
                'left':byte_manifest(left,'SHA256SUMS.txt')}
            handoff='inputs/handoff/krylov_remaining_conjectures_handoff/'
            hfiles={n[len(handoff):]:d for n,d in current.items() if n.startswith(handoff)}
            report['nested_manifest_counts']['handoff']=byte_manifest(hfiles,'manifest/SHA256SUMS.txt')
            # The original ZIPs, not the public view, supply every executed file.
            trees={'current':current,'left':left}
            for branch,files in trees.items():
                for p in (ROOT/'src/frozen'/branch).rglob('*'):
                    if p.is_file():
                        name=p.relative_to(ROOT/'src/frozen'/branch).as_posix()
                        require(files[name]==p.read_bytes(),'Private authority / public copy mismatch: '+name)
        else:
            payload=unpack((ROOT/'release_assets/v3-reproduction-view.zip').read_bytes())
            trees={branch:{n[len(branch)+1:]:d for n,d in payload.items() if n.startswith(branch+'/')}
                   for branch in ['current','left']}
        with tempfile.TemporaryDirectory(prefix='krylov-replay-') as tmp:
            tmp=Path(tmp)
            for branch,files in trees.items(): materialize(files,tmp/branch)
            # Load all saved expectations before any verifier can overwrite a result.
            expected={(branch,result):json.loads(trees[branch][result]) for _,branch,_,result in JOBS}
            for phase,branch,script,result in JOBS:
                tag=branch+'-'+Path(script).stem
                log(f'{phase}: {tag} START')
                started=time.monotonic()
                process=subprocess.run([sys.executable,str(tmp/branch/script)],cwd=tmp/branch,
                    env=child_environment(),capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=args.timeout)
                console=(process.stdout+process.stderr).replace(str(tmp),'<DISPOSABLE>')
                (out/(tag+'.log')).write_text(console,encoding='utf-8')
                row={'id':tag,'phase':phase,'returncode':process.returncode,
                     'script_sha256':digest(trees[branch][script]),'seconds':round(time.monotonic()-started,3),
                     'status':'FAIL','result':result}
                report['jobs'].append(row)
                require(process.returncode==0,'Frozen verifier failed: '+tag)
                observed=load(tmp/branch/result)
                same(expected[(branch,result)],observed,tag)
                save(out/(tag+'.json'),observed)
                row['status']='PASS'; row['matches_frozen_result']=True
                log(f'{phase}: {tag} PASS')
        report['disposable_work_directory_removed']=True
        report['status']='PASS'
    except Exception as error:
        report['error']=type(error).__name__+': '+str(error)
        log('FAIL: '+report['error'])
    finally:
        try:
            report['integrity_after']=verify_repo(args.private_assets)
            report['pristine_assets_unchanged']=True
        except Exception as error:
            report['status']='FAIL'; report['pristine_assets_unchanged']=False
            report['post_integrity_error']=str(error)
        save(out/'summary.json',report)
        log('REPRODUCTION '+report['status'])
        (out/'execution.log').write_text('\n'.join(lines)+'\n',encoding='utf-8')
    print('Result directory: '+str(out))
    return 0 if report['status']=='PASS' else 1


if __name__=='__main__':
    raise SystemExit(main())
