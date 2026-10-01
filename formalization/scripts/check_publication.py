#!/usr/bin/env python3
"""Check publication invariants independently of generated build outputs."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1]
repo=root.parent
baseline=json.loads((root/'verification/publication-baseline.json').read_text())
manifest=(root/'verification/proof-source-sha256.txt').read_bytes()
assert hashlib.sha256(manifest).hexdigest()==baseline['frozen_proof_manifest_sha256']
rows=[line.split('  ',1) for line in manifest.decode().splitlines()]
assert len(rows)==baseline['frozen_proof_file_count']==99
for expected,rel in rows:
 assert hashlib.sha256((root/rel).read_bytes()).hexdigest()==expected,rel
actual={p.relative_to(root).as_posix() for p in (root/'Krylov').glob('*.lean')}|{'Krylov.lean','Audit.lean','SemanticDependencies.lean'}
assert actual=={rel for _,rel in rows}
assert root.name=='formalization'
for rel,expected in baseline['unchanged_existing_files'].items():
 assert hashlib.sha256((repo/rel).read_bytes()).hexdigest()==expected,rel
workflow=(repo/'.github/workflows/lean-verification.yml').read_text()
assert 'working-directory: formalization' in workflow
assert 'formalization-v4/' not in workflow
assert 'bash scripts/verify_v4.sh' in workflow or 'run: ./scripts/verify_v4.sh' in workflow
print(json.dumps({'passed':True,'proof_files_unchanged_from_frozen_rc2':len(rows),'existing_files_unchanged':len(baseline['unchanged_existing_files']),'manuscript_and_pdfs_unchanged':True,'formalization_path':'formalization'},indent=2))
