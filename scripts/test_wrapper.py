"""Focused failure-injection checks for the repository wrapper, not mathematics."""
from pathlib import Path
import io
import json
import shutil
import subprocess
import sys
import tempfile
import zipfile
from reproduce import same
from staging_common import ROOT, require, unpack, child_environment


def main():
    results=[]
    with tempfile.TemporaryDirectory(prefix='krylov-negative-') as temp:
        temp=Path(temp).resolve()
        copy=temp/'repo'
        shutil.copytree(ROOT,copy,ignore=shutil.ignore_patterns('.git','.local','.venv','__pycache__'))
        target=copy/'release_assets/v3-reproduction-view.zip'
        original=target.read_bytes()
        target.write_bytes(original+b'FAILURE_INJECTION')
        p=subprocess.run([sys.executable,str(copy/'scripts/reproduce.py'),'--output',str(temp/'result')],
                         cwd=copy,env=child_environment(),capture_output=True,text=True)
        report=json.loads((temp/'result/summary.json').read_text())
        require(p.returncode!=0 and report['status']=='FAIL' and 'Hash mismatch' in report['error']
                and report['jobs']==[], 'Corrupted asset was not rejected before execution')
        results.append('tampered_release_asset_rejected_before_execution')
        target.write_bytes(original)
        forbidden=copy/'src/frozen/would-mutate'
        p=subprocess.run([sys.executable,str(copy/'scripts/reproduce.py'),'--output',str(forbidden)],
                         cwd=copy,env=child_environment(),capture_output=True,text=True)
        require(p.returncode!=0 and not forbidden.exists(), 'Unsafe output path accepted')
        results.append('output_inside_frozen_source_rejected')
    for expected,observed,label in [
        ({'gap':'4192/74529'},{'gap':'4193/74529'},'exact_rational_mismatch'),
        ({'x':1.0},{'x':1.01},'numerical_mismatch'),
        ({'x':1.0},{'x':float('nan')},'nan_rejected'),
        ({'x':True},{'x':1},'bool_integer_type_mismatch')]:
        try: same(expected,observed)
        except ValueError: results.append(label)
        else: raise RuntimeError('Mismatch accepted: '+label)
    buffer=io.BytesIO()
    with zipfile.ZipFile(buffer,'w') as z: z.writestr('../escape.txt','test')
    try: unpack(buffer.getvalue())
    except ValueError: results.append('zip_traversal_rejected')
    else: raise RuntimeError('Unsafe ZIP accepted')
    print(json.dumps({'status':'PASS','tests':results},indent=2))


if __name__=='__main__':
    main()
