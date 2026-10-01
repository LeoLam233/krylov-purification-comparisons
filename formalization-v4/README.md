# Krylov Lean formalization v4

Targeted release hardening of the frozen v3 candidate for authoritative manuscript commit `ea43fcc3fc033d7c6ce0887d5747c05868879508` in [LeoLam233/krylov-purification-comparisons](https://github.com/LeoLam233/krylov-purification-comparisons).

Lean 4.19.0 (official release commit `6caaee842e94`); mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All dependency Git revisions are locked by `lake-manifest.json`.

## What v4 changes

- Final canonical-source family wrappers in `Krylov/CanonicalFamilySource.lean`, explicitly composing all four canonical spread bridges with v3 results
- Delta-general canonical C_M/K_I transport and robust, finite and cubic source endpoints in `Krylov/PerturbedSourceAPI.lean`
- Value-only per-root required-bridge gate, with a machine-readable root × bridge matrix and concrete dependency paths
- Pinned, source-only GitHub Actions workflow and reproducible source/trust/hash/coverage/ledger gates
- F-16 retained as a substantive equivalent consequence; literal all-file manifest coverage, including `CHANGED_FILES_FROM_V2.json`

All 94 original v3 proof modules remain byte-identical. No v3 mathematical theorem, quantifier or physical definition is edited. The frozen v3 input archive has SHA-256 `e56c5281a10887efc745fdc80722cd0a5c359c0cd15c7794779a9839effaf1ae`.

## Reproduce

From a source-only checkout with Lean/Lake 4.19.0, Python, Git and Bash:

```sh
lake exe cache get
python3 scripts/check_dependency_pins.py
./scripts/verify_v4.sh
```

`verify_v4.sh` rejects a prebuilt project tree. It builds modules through ordinary `lake build` in serial dependency order to control memory, runs a final `lake build`, then audits module-provenance axioms and the value-only semantic gate. Official pinned dependency caches are allowed. It verifies the checked-in proof-source manifest before and after execution. `scripts/check_reference.py /path/to/upstream/clone` compares every bundled source-reference byte against the frozen upstream commit.

## Evidence and limits

Read `RELEASE_HARDENING_V4.md`, `FINAL_ANSWERS.md`, `SOURCE.json`, `COVERAGE.md`, `GAP_MANIFEST.md`, and `SOURCE_CLAIM_LEDGER.tsv` for adjudication and exact validation status. Current v4 execution evidence is named `verification/v4-*`; inherited non-v4 logs describe the frozen v3 input and are not v4 execution evidence.

`Audit.lean` selects all project declarations by originating module, including private/generated logical declarations. It rejects unsafe theorem dependencies and permits only `propext`, `Classical.choice`, and `Quot.sound`. Compiler-generated unsafe runtime specializations are separately listed, not logical axioms. The semantic gate is evidence of proof-body wiring; independent semantic review is still necessary. No second independent Lean kernel or external human peer review is claimed.

`SHA256SUMS.txt` covers every distributed regular file except itself, including both changed-file ledgers. Build artifacts, dependency checkouts and toolchains are excluded from the source package. `verification/proof-source-sha256.txt` separately covers all production Lean modules, the umbrella and both audit/gate Lean files. See the release report for CI run identity and for any distinction between local kernel success and independent CI success.
