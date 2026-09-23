# Final public v0.1 assets

| Location | Role and authority |
|---|---|
| paper/main.pdf; release_assets/manuscript.pdf | Identical PDF bytes, rebuilt from the approved metadata/disclosure/packaging edits to audited RC1 |
| paper/main.tex, paper/sections/, paper/references.bib | Complete manuscript source; scientific content unchanged |
| release_assets/paper-source.zip | Source-only archive matching every current .tex and references.bib byte-for-byte |
| release_assets/v3-reproduction-view.zip | Unchanged curated V3 verifier/result view; SHA-256 remains the RC1 value; not a full authoritative freeze |
| docs/CONJECTURE1_COUNTEREXAMPLES.md; docs/conjecture1_counterexamples.tex; release_assets/Conjecture1_exact_counterexamples.pdf | Readable communication derivative of frozen Propositions 3.1–3.2, Theorem 3.3 and Appendix A; no new claim; TeX builds independently |
| provenance/CONJECTURE1_NOTE_SOURCE_MAP.md | Claim/equation mapping to the exclusive preceding public freeze |
| src/frozen/; certificates/ | Unchanged public mathematical code, expected results and exact certificates |
| audits/; clean_room/ | Public certification summaries and final release-gate metadata |
| PUBLIC_TREE.sha256 | Every distributable tree file except this manifest itself; excludes .git/, .local/, .venv/ and __pycache__/ |
| RELEASE_NOTES.md; FINAL_SCIENTIFIC_DELTA_AUDIT.md; FINAL_FILE_CHANGES.md | Release status, scientific preservation evidence and exact packaging changes |

release_assets/RELEASE_ASSETS.sha256 covers all files in release_assets/ except itself.
The outer final public ZIP hash seals the public-tree manifest; it is recorded in
the accompanying assembly report and ZIP checksum sidecar outside the Git tree.
The local commit hash is likewise reported outside its own commit to avoid circularity.

The full RC1, complete input bundle, V3/V2 freezes, original mathematical archives,
raw audit/clean-room packages, private prompts and third-party PDFs remain internal.
provenance/INPUT_ANCHORS.json, PRIVATE_ASSETS.sha256, V3_SOURCE_HASHES.json and
CERTIFICATION_HASHES.json retain original fingerprint metadata only.
See PUBLIC_PRIVATE_BOUNDARY.md and LICENSING.md.
