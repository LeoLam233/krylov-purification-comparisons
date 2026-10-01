#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification
python3 scripts/check_source.py | tee verification/v4-source-check.log
python3 scripts/check_coverage.py --require-closed | tee verification/v4-coverage-check.log
python3 scripts/check_source_ledger.py | tee verification/v4-source-ledger-check.json
python3 scripts/check_v3_preservation.py | tee verification/v4-v3-preservation.json
sha256sum -c verification/proof-source-sha256.txt | tee verification/v4-proof-hash-before.log
python3 scripts/hash_proofs.py > verification/v4-proof-source-before.txt
lean --version | tee verification/v4-toolchain.log
lake --version | tee -a verification/v4-toolchain.log
python3 - <<'PY' | tee verification/v4-clean-start.json
import json
from pathlib import Path
artifacts=list(Path('.lake/build').rglob('*.olean')) if Path('.lake/build').exists() else []
assert not artifacts, 'Source-only verification requires no project build artifacts'
print(json.dumps({'project_olean_count':len(artifacts),'source_only_start':True}))
PY
# Serial scheduling avoids out-of-memory failures; each invocation is lake build.
python3 scripts/serial_build.py 2>&1 | tee verification/v4-build.log
lake build 2>&1 | tee -a verification/v4-build.log
lake env lean -j2 Audit.lean 2>&1 | tee verification/v4-axioms.log
lake env lean -j2 SemanticDependencies.lean 2>&1 | tee verification/v4-semantic-dependencies.log
python3 scripts/extract_dependency_matrix.py | tee verification/v4-required-bridge-check.log
python3 scripts/check_gate_controls.py | tee verification/v4-gate-controls.json
sha256sum -c verification/proof-source-sha256.txt | tee verification/v4-proof-hash-after.log
python3 scripts/hash_proofs.py > verification/v4-proof-source-after.txt
cmp verification/v4-proof-source-before.txt verification/v4-proof-source-after.txt
