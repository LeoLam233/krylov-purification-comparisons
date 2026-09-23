# Final public v0.1 assets — not yet published

- v3-reproduction-view.zip is the unchanged RC1 curated view of byte-identical V3
  verifiers and expected results. It is not the complete V3 archive or a new freeze.
- paper-source.zip contains the final approved author/disclosure/packaging edits
  and the unchanged scientific TeX and bibliography. Extract, then compile main.tex.
- manuscript.pdf is the clean rebuilt PDF, byte-identical to ../paper/main.pdf.
- Conjecture1_exact_counterexamples.pdf is a two-page communication derivative of
  the frozen manuscript, with no new claim. Its independently compilable source is
  ../docs/conjecture1_counterexamples.tex; the readable Markdown and source mapping
  are ../docs/CONJECTURE1_COUNTEREXAMPLES.md and
  ../provenance/CONJECTURE1_NOTE_SOURCE_MAP.md. Compile the source alone with
  `tectonic conjecture1_counterexamples.tex` in an empty directory.

RELEASE_ASSETS.sha256 covers every file here except itself. The source ZIP contains
only TeX and BibTeX to preserve the unchanged verifier's source-archive contract.
Licenses travel alongside these assets in the final public package: ../LICENSE,
../LICENSE-CC-BY-4.0.md and ../LICENSING.md. Keep those notices with redistributed assets.
No third-party PDF, private archive, prompt, dependency binary or cache is included.
