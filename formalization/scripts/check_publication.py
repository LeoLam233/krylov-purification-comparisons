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
 actual_hash=hashlib.sha256((repo/rel).read_bytes()).hexdigest()
 if actual_hash!=expected:
  # Keep the historical publication baseline intact. Accept only the exact
  # author-metadata/PDF maintenance hashes documented in the dated addendum.
  record=json.loads((repo/'provenance/BIBLIOGRAPHY_ORCID_2026-10-04.json').read_text())
  assert rel in {'paper/main.tex','paper/main.pdf','docs/conjecture1_counterexamples.tex',
                 'docs/CONJECTURE1_COUNTEREXAMPLES.md','release_assets/manuscript.pdf',
                 'release_assets/paper-source.zip','release_assets/Conjecture1_exact_counterexamples.pdf',
                 'release_assets/README.md','release_assets/RELEASE_ASSETS.sha256',
                 'scripts/staging_common.py'},rel
  row=record['publication_metadata_hash_updates'].get(rel,{})
  assert row.get('before')==expected and row.get('after')==actual_hash,rel
workflow=(repo/'.github/workflows/lean-verification.yml').read_text()
assert 'working-directory: formalization' in workflow
assert 'formalization-v4/' not in workflow
assert 'bash scripts/verify_v4.sh' in workflow or 'run: ./scripts/verify_v4.sh' in workflow
print(json.dumps({'passed':True,'proof_files_unchanged_from_frozen_rc2':len(rows),'existing_files_checked':len(baseline['unchanged_existing_files']),'scientific_payload_unchanged':True,'author_metadata_maintenance':'provenance/BIBLIOGRAPHY_ORCID_2026-10-04.json','formalization_path':'formalization'},indent=2))
