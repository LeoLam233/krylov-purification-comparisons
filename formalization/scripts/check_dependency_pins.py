#!/usr/bin/env python3
"""Check all actual dependency Git HEADs against the immutable lockfile."""
import json,subprocess
from pathlib import Path
root=Path(__file__).resolve().parents[1]
m=json.loads((root/'lake-manifest.json').read_text())
rows=[]
for p in m['packages']:
 path=root/m['packagesDir']/p['name']
 actual=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
 assert actual==p['rev'],(p['name'],actual,p['rev'])
 rows.append({'name':p['name'],'expected':p['rev'],'actual':actual,'passed':True})
assert next(r['actual'] for r in rows if r['name']=='mathlib')=='c44e0c8ee63ca166450922a373c7409c5d26b00b'
print(json.dumps({'passed':True,'dependencies':rows},indent=2))
