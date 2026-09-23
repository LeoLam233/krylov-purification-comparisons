"""Replay the completed paper-stage checks without editing the staged paper."""
from pathlib import Path
import argparse
import shutil
import subprocess
import sys
import tempfile
from staging_common import (ROOT, require, save, load, verify_repo, check_snapshot,
                            output_directory, child_environment)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-assets')
    parser.add_argument('--output')
    args=parser.parse_args()
    out=output_directory(args.output,'paper-check',args.private_assets)
    report={'status':'FAIL','full_original_paper_check':False}
    try:
        report['integrity']=verify_repo(args.private_assets)
        report['snapshot']=check_snapshot()
        if args.private_assets:
            with tempfile.TemporaryDirectory(prefix='krylov-paper-check-') as tmp:
                tmp=Path(tmp)
                shutil.copytree(ROOT/'paper',tmp/'paper')
                shutil.copytree(ROOT/'scripts/paper_stage',tmp/'scripts')
                (tmp/'inputs').mkdir()
                bundle='Krylov_Codex_COMPLETE_INPUT_BUNDLE_2026-09-23.zip'
                shutil.copyfile(Path(args.private_assets)/bundle,tmp/'inputs'/bundle)
                for script in ['integrity_check.py','check_paper.py']:
                    p=subprocess.run([sys.executable,str(tmp/'scripts'/script)],cwd=tmp,
                        env=child_environment(),capture_output=True,text=True,encoding='utf-8',errors='replace')
                    (out/(script+'.log')).write_text((p.stdout+p.stderr).replace(str(tmp),'<DISPOSABLE>'),encoding='utf-8')
                    require(p.returncode==0,'Original paper-stage check failed: '+script)
                report['full_original_paper_check']=True
                report['paper_check']=load(tmp/'paper/checks/PAPER_CHECK_REPORT.json')
                report['input_integrity']=load(tmp/'paper/checks/INTEGRITY_REPORT.json')
        report['status']='PASS'
    except Exception as e:
        report['error']=str(e)
    finally:
        try: report['integrity_after']=verify_repo(args.private_assets)
        except Exception as e: report['status']='FAIL'; report['integrity_error']=str(e)
        save(out/'summary.json',report)
    print('PAPER CHECK '+report['status']+'; '+str(out))
    return 0 if report['status']=='PASS' else 1


if __name__=='__main__':
    raise SystemExit(main())
