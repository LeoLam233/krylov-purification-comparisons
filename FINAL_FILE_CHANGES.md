# Exact release-state sentence correction changes

Baseline commit: `9a5440d292b61db07df36fcd8bc2f5dae12542c1`.
Baseline public ZIP SHA-256: `99a603aca80f4264e003e9b1d40f6dcc30b0664a17833234ff18eb49b0f4b12f`.

Exactly **18 files changed; 96 are byte-identical**. No files are added, removed or
moved. The sole manuscript source change is the exact user-supplied Introduction
release-state sentence replacement. Full README, main.tex/AI disclosure and all
five note/source-map/check-record files remain byte-identical.

| Exact changed public path | Necessary reason |
|---|---|
| `CHANGELOG.md` | Prepend minimal correction entry; retain all earlier entries. |
| `FINAL_FILE_CHANGES.md` | List exact changed files against the immediately preceding freeze. |
| `FINAL_SCIENTIFIC_DELTA_AUDIT.md` | Update required NONE verdict and preservation evidence for this correction. |
| `PUBLIC_TREE.sha256` | Refresh changed file hashes; same public path coverage. |
| `RELEASE_METADATA.json` | Append exact sentence/baseline and record that no new search occurred. |
| `RELEASE_NOTES.md` | Prepend the release-state correction record; preserve previous history. |
| `RELEASE_VERIFICATION.md` | Refresh current correction verification summary. |
| `paper/checks/REVIEWED_CONTENT.json` | Refresh only Introduction fingerprint and append correction provenance; scientific records and scope positions unchanged. |
| `paper/main.pdf` | Clean rebuild required by the approved sentence replacement. |
| `paper/sections/01_introduction.tex` | Replace exactly the stale Introduction release-state sentence with the supplied wording; every other manuscript source byte unchanged. |
| `provenance/FINAL_APPROVED_PROSE_CHANGES.json` | Append exact authorized sentence substitution and current baseline. |
| `provenance/FINAL_SCIENTIFIC_DELTA_EVIDENCE.json` | Record strict source preservation, unchanged README/note, existing sweep provenance and updated asset hashes. |
| `release_assets/RELEASE_ASSETS.sha256` | Refresh only manuscript PDF and source-archive hashes. |
| `release_assets/manuscript.pdf` | Identical distributed copy of the rebuilt manuscript. |
| `release_assets/paper-source.zip` | Refresh archive; only sections/01_introduction.tex member bytes change. |
| `release_verification/CLEAN_PAPER_BUILD.json` | Record requested clean manuscript build. |
| `release_verification/PDF_INSPECTION.json` | Record visual inspection of reflowed pages and full-body text identity after the exact replacement. |
| `release_verification/PUBLIC_REPRODUCTION.json` | Record requested fresh 9/9 public replay; code and expectations unchanged. |

All mathematical source blocks, scripts, certificates, expected results, bibliography,
historical audit/clean-room files, licenses, CITATION.cff, public/private boundaries,
inventory, asset maps/instructions, V3 anchors and existing final-sweep records are
unchanged. Source line positions are retained. This corrects release-state prose;
it does not perform a new search or alter scientific priority/scope qualifications.

The local commit is amended with the preserved human author/committer identity and
Codex trailer. Git configuration, remotes and tags are unchanged. Five outer companion
outputs are regenerated: Krylov_purification_v0.1_PUBLIC.zip, its .zip.sha256 sidecar,
FINAL_PUBLIC_FREEZE_RECORD.json, FINAL_ASSEMBLY_REPORT.md and FINAL_DELIVERABLES.sha256.
They remain outside the Git/ZIP tree to avoid circular hashes. The prior freeze is
retained internally. No publication or external contact occurs.
