"""Compile in a new temporary directory, then retain only the finished PDF and build evidence."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--engine', default='tectonic', help='Tectonic executable (tested: 0.17.0)')
    ap.add_argument('--cache', help='Optional TECTONIC_CACHE_DIR')
    ap.add_argument('--offline', action='store_true')
    args = ap.parse_args()
    engine = str(Path(shutil.which(args.engine) or args.engine).resolve())
    paper = ROOT / 'paper'
    dest = paper / 'checks/build'
    dest.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    if args.cache:
        env['TECTONIC_CACHE_DIR'] = str(Path(args.cache).resolve())
    with tempfile.TemporaryDirectory(prefix='krylov-paper-build-') as tmp:
        tmp = Path(tmp)
        clean_source = tmp / 'source'
        clean_source.mkdir()
        shutil.copy2(paper / 'main.tex', clean_source / 'main.tex')
        shutil.copy2(paper / 'references.bib', clean_source / 'references.bib')
        shutil.copytree(paper / 'sections', clean_source / 'sections')
        # No prior .aux, .bbl or PDF is admitted as input to this build.
        # Type-1 TeX fonts are used; no operating-system font enumeration is needed.
        fc = tmp / 'fonts.conf'
        fc.write_text('<?xml version="1.0"?><!DOCTYPE fontconfig SYSTEM "fonts.dtd"><fontconfig></fontconfig>', encoding='utf-8')
        env['FONTCONFIG_FILE'] = str(fc)
        command = [engine, '--untrusted', '--keep-logs', '--keep-intermediates',
                   '--outdir', str(tmp)]
        if args.offline:
            command.append('--only-cached')
        command.append('main.tex')
        version = subprocess.run([engine, '--version'], capture_output=True, text=True, check=True).stdout.strip()
        result = subprocess.run(command, cwd=clean_source, env=env, capture_output=True, text=True, encoding='utf-8', errors='replace')
        console = result.stdout + result.stderr
        (dest / 'console.log').write_text(console, encoding='utf-8')
        for suffix in ['.log', '.aux', '.bbl', '.blg', '.out']:
            if (tmp / ('main' + suffix)).exists():
                shutil.copy2(tmp / ('main' + suffix), dest / ('main' + suffix))
        log = (tmp / 'main.log').read_text(encoding='utf-8', errors='replace') if (tmp / 'main.log').exists() else ''
        failures = re.findall(r'^!.*|.*(?:undefined references|Citation.*undefined|Reference.*undefined|Overfull \\[hv]box|Missing character).*', log, re.M)
        bbl = (tmp / 'main.bbl').read_text() if (tmp / 'main.bbl').exists() else ''
        expected_keys = set(re.findall(r'@\w+\{([^,]+),', (paper / 'references.bib').read_text()))
        built_keys = set(re.findall(r'\\bibitem\{([^}]+)\}', bbl))
        passed = result.returncode == 0 and not failures and built_keys == expected_keys and (tmp / 'main.pdf').exists()
        report = {'status': 'PASS' if passed else 'FAIL', 'engine': version,
                  'clean_build_directory': True, 'offline': args.offline,
                  'clean_source_copy_excludes_generated_files': True,
                  'returncode': result.returncode, 'latex_failures': failures,
                  'bibliography_keys': sorted(built_keys), 'all_bibliography_entries_resolved': built_keys == expected_keys,
                  'command': command}
        if passed:
            shutil.copy2(tmp / 'main.pdf', paper / 'main.pdf')
            report['pdf_sha256'] = hashlib.sha256((paper / 'main.pdf').read_bytes()).hexdigest()
            # Generated BibTeX output helps readers inspect the finished bibliography.
            shutil.copy2(tmp / 'main.bbl', paper / 'main.bbl')
        (paper / 'checks/BUILD_REPORT.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
        print(console)
        print(json.dumps(report, indent=2))
        if not passed:
            raise SystemExit(1)


if __name__ == '__main__':
    main()
