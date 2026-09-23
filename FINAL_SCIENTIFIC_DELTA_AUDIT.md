# Final scientific delta audit: one release-state sentence

SCIENTIFIC DELTA: NONE

**FINAL PUBLIC v0.1 PACKAGE RE-FROZEN WITH CONJECTURE-1 COMMUNICATION NOTE — NOT YET PUBLISHED**

The baseline is commit `9a5440d292b61db07df36fcd8bc2f5dae12542c1`, ZIP SHA-256
`99a603aca80f4264e003e9b1d40f6dcc30b0664a17833234ff18eb49b0f4b12f`, manuscript PDF SHA-256
`8c6b6183d8375cc0a87146809e7efa4799194da24d01d6eb95f17112a0695dbe`. Git/ZIP/tree contents, all 114 public files,
the 113-entry manifest and companion hashes matched before editing. The preceding
complete public freeze and companion records remain preserved internally.

## Sole authorized correction

The complete stale sentence beginning “A broad public-prior-art search…” and ending
“a fresh search remains necessary before public release.” is replaced with exactly:

> A final fresh public-prior-art sweep before release found no matching public prior result; absolute priority is not claimed.

This is a release-state correction supported by the existing frozen
audits/RELEASE_GATES.md record. It performs no fresh search and does not renew the
recorded cutoff or strengthen the priority claim. The exact before/after bytes are
in provenance/FINAL_APPROVED_PROSE_CHANGES.json. All other Introduction bytes and
source line positions are preserved. No other manuscript source file changes.

## Required preservation checks

| Check | Result |
|---|---|
| All 71 displayed equations | PASS: ordered raw-byte equation blocks unchanged |
| All 14 formal statements | PASS: theorem/proposition/lemma/corollary blocks unchanged |
| All 14 proof blocks | PASS: raw-byte proof blocks unchanged |
| Scientific constants, ranges, quantifiers, witnesses and families | PASS: full source equals baseline outside the one authorized non-scientific sentence; all 181 scope rows and positions unchanged |
| Other manuscript prose and AI disclosure | PASS: every other source byte, including main.tex, unchanged |
| Bibliography | PASS: references.bib and clean rebuilt main.bbl byte-identical; all five entries resolve |
| Code, certificates and expected results | PASS: every scripts/, src/ and certificates/ file and mathematical ZIP byte-identical |
| README | PASS: entire file byte-identical |
| Conjecture-1 note | PASS: Markdown, LaTeX, PDF, source map and check record all byte-identical |
| Historical audits, clean rooms and V3 authority | UNCHANGED: original files and scientific fingerprints retained |
| Novelty/priority | Only authorized release-state sentence updated; absolute priority remains unclaimed, frozen search qualifications and scientific positioning preserved |

The snapshot refreshes only the Introduction source fingerprint and appends a
release-state correction record. All scientific review records, equation/statement/
proof hashes and scope rows are unchanged. The 57 protected-file and 28 historically
verified V3-copy fingerprints match. No new mathematical audit or scientific claim
is introduced. The unchanged note retains its historical source mapping, including
the note-creation baseline's Introduction fingerprint; its mapped hierarchy equation
is byte-identical and this release-state prose correction is recorded separately.

## Build, visual inspection and replay

Clean manuscript build: **PASS**, Tectonic 0.17.0 offline in a new empty compiler
source/build directory, admitting only final TeX and unchanged BibTeX. No old PDF,
.aux or .bbl is an input. The existing verified tool environment is reused.
Both distributed manuscript PDF copies equal the clean output.

All 16 pages were rendered with Poppler. The shorter sentence causes pagination
reflow on pages 2–9; all eight changed pages were directly inspected and render
cleanly, with no clipping, overlap, missing glyph or overfull box. Pages 1 and
10–16 are pixel-identical to the inspected baseline. The full extracted PDF body
equals the baseline after only the exact authorized sentence replacement, ignoring
page-number footers, extraction ligatures and whitespace.

New manuscript PDF SHA-256: `dd7bdad1912b4660e231e507a0d8002d3077703ef8e4d6eefb6e139f19584efe`.

Public reproduction: **9/9 PASS**, with unchanged scripts, expected outputs,
dependency pins and comparison policies. The five exact, three legacy mixed and
one non-rigorous numerical classifications remain unchanged. The public paper
checker also passes (71 displays, 14 statements, 181 scope rows); its identical
summary is retained without rewriting. The unchanged note was not rebuilt.
Its existing successful build, inspection and derivative-content evidence is retained.

Note classification: **DERIVATIVE SCIENTIFIC CONTENT ONLY — NO NEW CLAIM**.
Unchanged note PDF SHA-256: `cc6a7892b5fd3febff5d9d03cbbe75aed3c104075e6ed8925ae551b986fa39de`.

## Derived records and local freeze

Only the approved sentence and necessarily derived assets, hashes/manifests,
release/change records and verification evidence are refreshed. Exactly 18 public
files change; 96 remain byte-identical; no files are added, removed or moved.
FINAL_FILE_CHANGES.md lists exact paths/reasons. Existing licenses, CITATION.cff,
inventory, asset instructions/maps and public/private boundaries remain unchanged.
Third-party exclusions remain effective.

Both Git identities remain `Dehao Lin <115764367+LeoLam233@users.noreply.github.com>` with exact trailer `Co-authored-by: Codex <noreply@openai.com>`.
The amended commit and outer ZIP hash are recorded in companion outputs outside
their own hash boundary. No remote, push, tag, publication, release, author contact,
email or manuscript submission occurs.

SCIENTIFIC DELTA: NONE
