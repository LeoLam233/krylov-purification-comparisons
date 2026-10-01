#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification
python3 scripts/check_source.py | tee verification/source-check.log
python3 scripts/check_coverage.py --require-closed | tee verification/coverage-check.log
lean --version | tee verification/toolchain.log
python3 scripts/hash_proofs.py > verification/proof-source-sha256.before.txt
python3 scripts/serial_build.py 2>&1 | tee verification/build.log
lake env lean -j2 Audit.lean 2>&1 | tee verification/axioms.log
lake env lean -j2 SemanticDependencies.lean 2>&1 | tee verification/semantic-dependencies.log
python3 scripts/hash_proofs.py > verification/proof-source-sha256.txt
cmp verification/proof-source-sha256.before.txt verification/proof-source-sha256.txt
printf '%s\n' 'PASS: proof sources remained unchanged throughout build and axiom audit' | tee verification/source-stability.log
