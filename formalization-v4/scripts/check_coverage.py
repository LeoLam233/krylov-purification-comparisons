#!/usr/bin/env python3
"""Check source-label inventory and mutually exclusive ledger categories.
This checks bookkeeping, not mathematical semantic equivalence.
"""
from pathlib import Path
import re
import sys
root = Path(__file__).resolve().parent.parent
ledger = (root / 'GAP_MANIFEST.md').read_text()
expected = {}
for path in sorted((root / 'source-reference').glob('*.tex')):
    for label in re.findall(r'\\label\{((?:eq|thm|prop|lem|cor):[^}]+)\}', path.read_text()):
        expected[f'{path.name}:{label}'] = label
rows = {}
for line in ledger.splitlines():
    if not line.startswith('|'):
        continue
    m = re.match(r'\|\s*`?([^|`]+\.tex:(?:eq|thm|prop|lem|cor):[^|`]+)`?\s*\|\s*([ABCD])\s*\|', line)
    if m:
        key = m.group(1).strip()
        if key in rows:
            raise SystemExit('FAIL: duplicate source row: ' + key)
        rows[key] = m.group(2)
missing = set(expected) - set(rows)
extra = set(rows) - set(expected)
if missing or extra:
    raise SystemExit(f'FAIL: missing={sorted(missing)}, extra={sorted(extra)}')
counts = {c: sum(v == c for v in rows.values()) for c in 'ABCD'}
eqs = sum(label.startswith('eq:') for label in expected.values())
claims = len(expected) - eqs
print(f'PASS: {eqs} source displays and {claims} named mathematical statements have exactly one ledger category')
print('Categories:', counts)
print('Semantic correspondence requires the accompanying proofs and review; this inventory check alone does not certify it')

if '--require-closed' in sys.argv:
    residuals = [line.split('|')[1].strip() for line in ledger.splitlines()
                 if re.match(r'^\|[^|]+\|\s*C\s*\|', line)]
    if residuals:
        raise SystemExit('FAIL: retained statements still marked C: ' + '; '.join(residuals))
    print('CLOSURE LEDGER CHECK PASSED: no retained mathematical statement marked missing')
