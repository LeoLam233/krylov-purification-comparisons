#!/usr/bin/env python3
"""Check the independent source-row inventory, not semantic truth."""
from pathlib import Path
import csv,json
root=Path(__file__).resolve().parents[1]
with (root/'external-audit/CLAIM_AUDIT.tsv').open(encoding='utf-8') as f:
    prior=list(csv.DictReader(f,delimiter='\t'))
with (root/'SOURCE_CLAIM_LEDGER.tsv').open(encoding='utf-8') as f:
    current=list(csv.DictReader(f,delimiter='\t'))
assert len(current)==len(prior)==128
old={r['id']:r for r in prior}
assert len({r['id'] for r in current})==128
assert set(old)=={r['id'] for r in current}
for r in current:
    assert r['source_locator']==old[r['id']]['source_locator'],r['id']
    assert r['source_statement']==old[r['id']]['source_statement'],r['id']
    assert r['v4_category'] in {'A','B','D'},r['id']
    assert r['lean_evidence'].strip() not in {'','-'},r['id']
print(json.dumps({'rows':len(current),'unique_ids':True,'source_locators_and_statements_preserved':True,'remaining_category_C':0,'categories':{c:sum(r['v4_category']==c for r in current) for c in 'ABCD'},'scope':'bookkeeping only; semantic correspondence is supplied by checked Lean derivations and the scoped reviews'},indent=2))
