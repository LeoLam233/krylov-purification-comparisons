# Release-audit wording repairs (local, unreleased)

This copy applies the two repairs recorded before editing in RELEASE_CLAIM_AUDIT.md,
RELEASE_CLAIM_LEDGER.json and REQUIRED_REPAIRS.md in the accompanying audit outputs.

- RR-01: paper/sections/04_factor_two.tex:52 now names C_K and C_S as the complexities
  with coefficients 2v and v. The displayed sides C_K and 2 C_S have equal leading coefficients.
- RR-02: paper/sections/01_introduction.tex:41 removes "last" so the two concentration
  questions correctly refer to r and q.

All 71 displayed equations, all 14 formal statements, constants, hypotheses, parameter ranges
and mathematical verifier files retain their original bytes. No scientific delta relative to
V3 was introduced. The PDF is rebuilt and source/PDF assets and content manifests are refreshed.
This is a release-claim wording correction, not a new scientific freeze or RC1.

The original supplied ZIPs remain immutable. In the repository, COPY_MAP.json continues to
list only byte-identical source copies; provenance/RELEASE_REPAIR_MAP.json separately records
changed copied files with original and current hashes. Historical paper-stage reports and
staging reproduction/ reports retain their original dated meaning and are not second-pass
release-audit reports. REVIEWED_CONTENT.json retains its original review plus an explicit
release-audit update for the two prose changes.

Original input and certification archives are not added to the public repository. The original
staging private-sibling inventory is metadata; that sibling directory is not supplied in the
repository ZIP. The complete authoritative input remains embedded unchanged in the paper copy.
RC1, final priority sweep, publication, contact, email and submission are outside this run.
