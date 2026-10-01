#!/usr/bin/env python3
"""Extract the kernel-environment value-only gate matrix; fail closed."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
expected=json.loads((root/'verification/required-bridges.json').read_text())
rows=[]
for line in (root/'verification/v4-semantic-dependencies.log').read_text().splitlines():
    tag='REQUIRED_BRIDGE_JSON '
    if tag in line: rows.append(json.loads(line.split(tag,1)[1]))
pairs={(r['root'],b) for r in expected['requirements'] for b in r['required_bridges']}
assert len(rows)==len(pairs),('missing or duplicate pairs',len(rows),len(pairs))
assert {(r['root'],r['required_bridge']) for r in rows}==pairs
for r in rows:
    assert r['traversal']=='value-only' and r['reachable'] is True
    assert r['path'][0]==r['root'] and r['path'][-1]==r['required_bridge']
(root/'verification/v4-required-bridge-matrix.json').write_text(json.dumps({'passed':True,'traversal':'value-only','rows':rows},indent=2)+'\n')
print(f'PASS: {len(rows)} value-only required-bridge paths for {len(expected["requirements"])} final roots')
