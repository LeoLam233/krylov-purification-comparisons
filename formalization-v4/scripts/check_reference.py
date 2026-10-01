#!/usr/bin/env python3
"""Compare bundled reference bytes with the pinned upstream Git objects.
Usage: python3 scripts/check_reference.py /path/to/upstream/clone
This is a source-provenance check, not a proof of mathematical correspondence.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
if len(sys.argv) != 2:
    raise SystemExit(__doc__)
repo = Path(sys.argv[1]).resolve()
commit = json.loads((root / 'SOURCE.json').read_text())['commit']
rows = []
for path in sorted((root / 'source-reference').rglob('*')):
    if not path.is_file():
        continue
    name = path.name
    if path.parent.name == 'communication':
        upstream = 'docs/' + name
    elif name == 'main.tex':
        upstream = 'paper/main.tex'
    elif path.suffix == '.tex':
        upstream = 'paper/sections/' + name
    elif name in {'CLAIM_SOURCE_MAP.md', 'NOTATION_MAP.md'}:
        upstream = 'paper/' + name
    elif name == 'DISPLAY_AND_QUANTIFIER_AUDIT.md':
        upstream = 'paper/checks/' + name
    else:
        upstream = name
    data = subprocess.check_output(['git', '-C', str(repo), 'show', commit + ':' + upstream])
    actual = path.read_bytes()
    if actual != data:
        raise SystemExit('FAIL: reference mismatch: ' + name)
    rows.append({'reference': str(path.relative_to(root)), 'upstream_path': upstream,
                 'sha256': hashlib.sha256(actual).hexdigest(), 'byte_identical': True})
print(json.dumps({'upstream_commit': commit, 'references': rows,
                  'claim_mapping': 'GAP_MANIFEST.md',
                  'semantic_review': ['V3_SEMANTIC_REVIEW.md', 'V3_QUBIT_REVIEW.md']}, indent=2))
