"""Build a disposable copy with the unchanged paper-stage build script."""
from pathlib import Path
import argparse
import shutil
import subprocess
import sys
import tempfile
from staging_common import ROOT, require, save, load, verify_repo, check_snapshot, output_directory, child_environment


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--engine',default='tectonic',help='Tectonic executable; tested with 0.17.0')
    ap.add_argument('--cache',help='Optional populated Tectonic cache')
    ap.add_argument('--offline',action='store_true')
    ap.add_argument('--output',help='New output directory, default .local/paper-build-TIMESTAMP')
    args=ap.parse_args()
    out=output_directory(args.output,'paper-build')
    report={'status':'FAIL'}
    try:
        report['integrity_before']=verify_repo()
        report['snapshot']=check_snapshot()
        engine=str(Path(shutil.which(args.engine) or args.engine).resolve())
        with tempfile.TemporaryDirectory(prefix='krylov-build-wrapper-') as tmp:
            tmp=Path(tmp)
            shutil.copytree(ROOT/'paper',tmp/'paper')
            (tmp/'scripts').mkdir()
            shutil.copyfile(ROOT/'scripts/paper_stage/build.py',tmp/'scripts/build.py')
            command=[sys.executable,str(tmp/'scripts/build.py'),'--engine',engine]
            if args.cache: command+=['--cache',str(Path(args.cache).resolve())]
            if args.offline: command.append('--offline')
            process=subprocess.run(command,cwd=tmp,env=child_environment(),capture_output=True,
                                   text=True,encoding='utf-8',errors='replace')
            (out/'execution.log').write_text(process.stdout+process.stderr,encoding='utf-8')
            require(process.returncode==0,'Original clean-build script failed')
            report['build']=load(tmp/'paper/checks/BUILD_REPORT.json')
            require(report['build']['status']=='PASS','Paper build gate failed')
            for name in ['main.pdf','main.bbl']:
                shutil.copyfile(tmp/'paper'/name,out/name)
            shutil.copytree(tmp/'paper/checks/build',out/'build')
        report['status']='PASS'
        report['staged_manuscript_not_replaced']=True
        report['limit']='PDF metadata may differ; source/PDF originals remain unchanged.'
    except Exception as e:
        report['error']=str(e)
    finally:
        try: report['integrity_after']=verify_repo()
        except Exception as e: report['status']='FAIL'; report['integrity_error']=str(e)
        save(out/'summary.json',report)
    print('PAPER BUILD '+report['status']+'; '+str(out))
    return 0 if report['status']=='PASS' else 1


if __name__=='__main__':
    raise SystemExit(main())
