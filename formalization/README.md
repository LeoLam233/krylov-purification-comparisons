# Lean formalization

This directory formalizes the retained mathematical claims at manuscript commit
`ea43fcc3fc033d7c6ce0887d5747c05868879508`. It contains the byte-identical proof
payload of the frozen v4 RC2 candidate, published in a stable repository layout.
Internal v3/v4 labels describe formalization history, not public release versions.

## Scope and entry points

- `Krylov.lean` imports all 96 production modules
- `Krylov/CanonicalFamilySource.lean` exports final canonical-source temporal-family endpoints
- `Krylov/PerturbedSourceAPI.lean` exports delta-general canonical perturbed-witness endpoints
- [COVERAGE.md](COVERAGE.md), [GAP_MANIFEST.md](GAP_MANIFEST.md), and
  [SOURCE_CLAIM_LEDGER.tsv](SOURCE_CLAIM_LEDGER.tsv) map retained claims to proofs
- [SOURCE.json](SOURCE.json) records immutable source, toolchain, and historical CI identities
- [HISTORY.md](HISTORY.md) records repairs and review limitations

The scope is not every sentence, intermediate proof step, historical statement, or
priority claim. Equivalent proofs and consequences are identified in the ledger.
No new manuscript theorem is asserted by this publication.

## Reproduce from source

Requirements: Lean/Lake 4.19.0, Python 3, Git, Bash, and `sha256sum`. The repository
pins `leanprover/lean4:v4.19.0`; mathlib is
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, with every dependency pinned in
[lake-manifest.json](lake-manifest.json). An existing elan installation can install
the exact toolchain with `elan toolchain install leanprover/lean4:v4.19.0`.
CI instead downloads the official Linux release archive and checks its SHA-256
`6fe3ce97a58f44e2b3567d455b994eacec5bfe9ae7774f2a573444480ba813fe`.

From a fresh clone, before building any project module:

```sh
python3 scripts/verify_assets.py
cd formalization
lake exe cache get
python3 scripts/check_dependency_pins.py
python3 scripts/check_reference.py ..
python3 scripts/check_publication.py
bash scripts/verify_v4.sh
```

Run the original Python certificate replay in a separate fresh checkout as described
in the top-level README. It needs no private archive for its public replay.

The Lean script deliberately rejects existing project `.olean` files. To repeat a
source-only verification, use a fresh clone; pinned dependency caches are permitted.
The script schedules ordinary `lake build` invocations serially for bounded memory,
then runs a final `lake build`. It does not bypass the kernel or substitute a numerical
oracle. Allow substantial time for a clean run; GitHub's job limit is 180 minutes.

## Verification layers

1. Dependency revisions and authoritative manuscript-reference bytes are checked
2. Source/trust scans reject holes, new axioms, unsafe/oracle shortcuts and kernel bypasses
3. Every production module and umbrella is kernel-compiled from zero project artifacts
4. `Audit.lean` selects declarations by originating module, including private/generated
   declarations. It rejects unsafe logical dependencies and checks the reachable axiom
   union is exactly `propext`, `Classical.choice`, `Quot.sound`. Compiler-generated unsafe
   runtime specializations are classified separately, not treated as logical axioms
5. Coverage checks match 71 displays and 14 named statements; the larger source ledger
   has 128 rows. These bookkeeping checks alone do not establish semantic equivalence
6. `SemanticDependencies.lean` follows proof values only. Its 22 final source roots must
   each reach four tailored bridges (88 pairs). Missing roots, missing bridges, type-only
   references and unrelated bridges are tested as rejecting negative controls
7. SHA-256 checks cover 99 proof/audit inputs before and after verification; all original
   94 v3 production proof modules must remain byte-identical
8. The publication guard checks the frozen proof manifest, stable paths and unchanged
   manuscript payload

## Evidence and limitations

The frozen proof payload passed [run 36866846382](https://github.com/LeoLam233/krylov-purification-comparisons/actions/runs/36866846382):
97 built modules, 3,088 safe declarations, 2,606 theorem constants, all 88 semantic
pairs, and four rejecting controls. Its artifact digest is recorded in `SOURCE.json`.
The [publication workflow](https://github.com/LeoLam233/krylov-purification-comparisons/actions/workflows/lean-verification.yml)
runs the full gates again for the final directory layout. Consult the run attached
to the exact release/main commit for final publication evidence.

Generated logs and machine-readable matrices are uploaded as CI artifacts and written
under `verification/v4-*` locally. They are not checked in as stale success evidence.
The value-only graph establishes required syntactic proof dependencies, while scoped
source review addresses mathematical interpretation. No external human peer review,
second independent kernel, or renewed literature-priority audit is claimed.
