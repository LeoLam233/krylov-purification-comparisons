# Verification inputs and generated evidence

Checked-in inputs:
- `proof-source-sha256.txt`: frozen SHA-256 for all 99 Lean proof/audit inputs
- `required-bridges.json`: expected 22-root / 88-pair semantic matrix
- `v3-proof-baseline.json`: original 94 production-module hashes and frozen archive digest
- `publication-baseline.json`: publication invariants and immutable proof-manifest digest

`bash scripts/verify_v4.sh` generates `v4-*` logs, JSON matrices, controls and before/after
hash manifests. CI uploads these even on failure. Generated output is ignored by Git.
Run identity and conclusion must be read from GitHub; a historical log is not evidence
that a later checkout has passed. Immutable historical identities are in `../SOURCE.json`.
