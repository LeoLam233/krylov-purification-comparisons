# Public v0.1.2 assets (mathematical payload unchanged from v0.1.1)

| Location | Role and authority |
|---|---|
| paper/main.pdf; release_assets/manuscript.pdf | Identical PDF bytes, cleanly rebuilt with approved reader-facing wording and unchanged mathematics |
| paper/main.tex, paper/sections/, paper/references.bib | Complete manuscript source; scientific content unchanged |
| release_assets/paper-source.zip | Source-only archive matching every current .tex and references.bib byte-for-byte |
| release_assets/v3-reproduction-view.zip | Unchanged curated V3 verifier/result view; SHA-256 remains the RC1 value; not a full authoritative freeze |
| docs/CONJECTURE1_COUNTEREXAMPLES.md; docs/conjecture1_counterexamples.tex; release_assets/Conjecture1_exact_counterexamples.pdf | Readable communication derivative of frozen Propositions 3.1–3.2, Theorem 3.3 and Appendix A; no new claim; TeX builds independently |
| provenance/CONJECTURE1_NOTE_SOURCE_MAP.md | Claim/equation mapping to the communication-note pre-publication baseline; the note survived unchanged into public v0.1 |
| src/frozen/; certificates/ | Unchanged public mathematical code, expected results and exact certificates |
| audits/; clean_room/ | Public certification summaries and final release-gate metadata |
| PUBLIC_TREE.sha256 | Every distributable tree file except this manifest itself; excludes .git/, .local/, .venv/ and __pycache__/ |
| RELEASE_NOTES.md; FINAL_SCIENTIFIC_DELTA_AUDIT.md; FINAL_FILE_CHANGES.md | Release status, scientific preservation evidence and exact packaging changes |

release_assets/RELEASE_ASSETS.sha256 covers all files in release_assets/ except itself.
The v0.1 publication commit and final asset hashes are inspectable in the [public-safe Markdown](release_verification/PUBLICATION_VERIFICATION_REPORT.md) and [JSON](release_verification/PUBLICATION_VERIFICATION_REPORT.json) derivatives of the contemporaneous outer reports. The current v0.1.2 ZIP hash is in its checksum sidecar and GitHub Release. The exact v0.1.1 commit `6362c93194b723fb397569882b4a9ca4de6f2b7c`, tag target, and release-asset digests are publicly inspectable through [GitHub history](https://github.com/LeoLam233/krylov-purification-comparisons/commit/6362c93194b723fb397569882b4a9ca4de6f2b7c) and the [v0.1.1 Release](https://github.com/LeoLam233/krylov-purification-comparisons/releases/tag/v0.1.1).

The full RC1, complete input bundle, V3/V2 freezes, original mathematical archives,
raw audit/clean-room packages, private prompts and third-party PDFs remain internal.
provenance/INPUT_ANCHORS.json, PRIVATE_ASSETS.sha256, V3_SOURCE_HASHES.json and
CERTIFICATION_HASHES.json retain original fingerprint metadata only.
See PUBLIC_PRIVATE_BOUNDARY.md and LICENSING.md.
