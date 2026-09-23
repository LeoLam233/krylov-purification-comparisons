# Reproduction and build contract

This interface replays frozen evidence; it does not add claims or conduct a
release-level claim audit. Run commands from the public Git root `Krylov_purification_v0.1/`.
The accompanying release audit separately records two prose corrections and rebuilt assets;
see RELEASE_AUDIT_CHANGES.md. Historical reproduction/ records remain in internal RC1;
selected final run summaries are in release_verification/.

## Environment and entry points

Use Python 3.11 or newer in a virtual environment. Install the exact versions in
`requirements.txt`: SymPy 1.14.0, NumPy 2.3.5, SciPy 1.17.0 and mpmath 1.3.0.
Package installation may need network access; the reproduction itself does not.
Do not use Python `-O`: frozen verifier assertions must remain enabled.

```text
python -m venv .venv
# Activate .venv using the command appropriate to your shell.
python -m pip install -r requirements.txt
python scripts/verify_assets.py
python scripts/reproduce.py
python scripts/test_wrapper.py
```

The default command verifies the public release assets and all unchanged
copy-view files, extracts `release_assets/v3-reproduction-view.zip` into a fresh
temporary directory, executes nine frozen scripts, compares their JSON results
against frozen expectations, verifies original assets again, and removes the
temporary directory. Source strings, integers, booleans and structures compare
exactly. JSON floats use the original second-run replay's absolute/relative 1e-9
tolerance. The first-run explicitly numerical 90-digit diagnostic strings use
absolute 1e-75; their reported errors must also remain below 1e-75. Frozen internal
assertions and tighter numerical tolerances are still executed unchanged.

```text
python scripts/reproduce.py --private-assets ../Krylov_Private_Assets
python scripts/verify_assets.py --private-assets ../Krylov_Private_Assets
```

This mode verifies every private asset against its anchored manifest, verifies
the original mathematical and transferred-handoff manifests, and executes files
extracted from the original first- and second-run ZIPs. Every selected file is also
compared byte-for-byte with the public view. The private bundle is not needed for
the default public-view replay. V3 remains the authority in both modes; the curated
ZIP is explicitly a selected copy view, not an original archive or a new freeze.

Every run produces `summary.json`, an `execution.log`, per-job logs and reproduced
JSON under a new `.local/reproduction-*` directory. `--output PATH` selects a new
empty output directory. Outputs cannot overlap public frozen files or private
assets. Any hash, process, structure or value mismatch yields a nonzero exit.
The summary records mode, environment, comparison policy and before/after integrity.
The wrapper test command performs seven failure-injection checks on disposable copies.
The public-tree manifest excludes `.git/`, `.local/`, `.venv/` and Python bytecode caches.

## Exact and numerical evidence

| Phase | Frozen scripts | Interpretation |
|---|---|---|
| exact | clean_room_1r_search, verify_1r, derive_short_time, verify_target2_exact, verify_restricted_survivors | Replay of existing exact/symbolic checks; the historical search name does not mean a new clean-room run |
| legacy_mixed_exact_and_numerical | first-run verify.py, verify_1r_bootstrap, verify_factor_two | Original scripts interleave exact assertions and floating-point diagnostics. They remain byte-identical and are explicitly labeled mixed, never entirely rigorous numerical certificates |
| numerical_nonrigorous | verify_target2_numerical | Separate full-matrix, quadrature and high-precision point cross-checks; no theorem is inferred from numerical integration |

All nine scripts run; no difficult check is skipped. Expected results are loaded
before execution. Historical byproduct checks are replayed as frozen code only;
their inclusion does not enlarge the manuscript's retained claim set. The original
combined entry point is not modified or run in a pristine tree; the new wrapper
calls its component verifiers and additionally replays the first-run verifier.

The two CR0s and hostile audits are retained evidence, not regenerated here. Their
hashes, coverage limits and original private locations are documented separately.

## Paper checks and clean build

```text
python scripts/check_paper.py
python scripts/check_paper.py --private-assets ../Krylov_Private_Assets
python scripts/build_paper.py --engine tectonic
python scripts/build_paper.py --engine /path/to/tectonic --cache /path/to/cache --offline
```

The public check verifies the final manuscript source against its derived fingerprint
snapshot. Original scientific display, formal-statement and scope records remain unchanged;
only approved metadata/packaging source hashes are refreshed, as recorded in the final delta audit.
The private mode additionally replays the unchanged original integrity and paper
check scripts against the complete bundle in a temporary paper project. This covers
71 displays, 14 formal statements, 181 scope trigger lines, the mapped V3 hashes,
20 exact arithmetic checks and five citations. It checks the existing review; it
does not claim a fresh semantic review, release-level audit or human validation.

Tectonic 0.17.0 is tested. The original build script uses a clean source/build
directory, runs TeX/BibTeX to convergence and checks the final log. A populated
cache permits a fully offline build. Without it, Tectonic may fetch TeX resources.
Generated PDFs/logs go to `.local/paper-build-*`; the staged PDF and sources remain
unchanged. PDF metadata may change, so staging verification also compares rendered
pages with the supplied completed PDF. Compiler/cache binaries are tooling, not
scientific input or repository release assets.

## Known limits

Appendix C now states the approved internal/public archive boundary; see
`docs/STAGING_PATHS.md`. Authorship, disclosure, licenses and citation metadata are
supplied for this package. Full original private-mode checks require a separately
provisioned private layout and are not required for the default public replay.
The final assembly is a metadata-only delta audit, clean build and engineering
replay. It does not repeat research, hostile audits, clean-room certification or
priority searching. Publication is external to the reproduction workflow; these commands perform no
repository, release, author-contact, email, or submission actions.
