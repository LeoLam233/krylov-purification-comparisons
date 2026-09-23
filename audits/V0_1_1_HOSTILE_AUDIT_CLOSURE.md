# v0.1.1 public hostile-audit finding closure

This closure record addresses the frozen findings of the independent public v0.1 hostile audit. It is not a new mathematical audit. The external auditor has not yet reviewed v0.1.1; an independent regression audit is a separate later step.

**DOCUMENTATION / PROVENANCE PATCH ONLY**

**SCIENTIFIC DELTA: NONE**

| Finding | v0.1 severity | v0.1.1 disposition |
|---|---|---|
| A01 — inaccessible final publication reports | MODERATE | **CLOSED**: public-safe [Markdown](../release_verification/PUBLICATION_VERIFICATION_REPORT.md) and [JSON](../release_verification/PUBLICATION_VERIFICATION_REPORT.json) derivatives preserve the contemporaneous verification facts and original report hashes. Current pointers were corrected in `README.md`, `RELEASE_VERIFICATION.md`, `FINAL_SCIENTIFIC_DELTA_AUDIT.md`, `RELEASE_ASSET_MAP.md`, `RELEASE_METADATA.json`, `release_verification/PUBLICATION_CHECKS.json`, and `provenance/FINAL_SCIENTIFIC_DELTA_EVIDENCE.json`. The raw originals remain private. |
| A02 — unqualified historical release language | MINOR | **CLOSED**: `paper/BIBLIOGRAPHY_PROVENANCE.md`, `paper/CLAIM_SOURCE_MAP.md`, `provenance/SOURCE_PAPERS.md`, `RELEASE_AUDIT_CHANGES.md`, and `audits/RELEASE_GATES.md` now identify the relevant pre-publication stage or describe the existing public tree accurately. Exact before/after strings are below. The two changed paper documentation files were removed from the current byte-identical `COPY_MAP.json` and recorded with original/current hashes in [the copy-map delta](../provenance/V0_1_1_COPY_MAP_DELTA.json). Historical changelog and earlier substitution records remain dated history. |
| A03 — mislabeled note creation baseline | MINOR | **CLOSED**: `provenance/CONJECTURE1_NOTE_SOURCE_MAP.md` identifies `8f8262809efd6f270fce6cf4e3aa9c6fd38747bc` as the communication-note pre-publication baseline and names the actual public v0.1 commit `4a637eaf0cd6beeaab72afca62f8069fa01793be`. `RELEASE_ASSET_MAP.md` uses the same terminology. All note mathematics and other note files are byte-identical. |
| A04 — private raw audit outputs called accompanying | MINOR | **CLOSED**: `RELEASE_AUDIT_CHANGES.md` names the three raw files as private/non-distributed pre-publication outputs and links the public [release-gate summary](RELEASE_GATES.md) and [archive boundary](../PUBLIC_PRIVATE_BOUNDARY.md). The raw packages were not published. |
| A05 — two README AI disclosure passages | COSMETIC | **NO ACTION — intentional two-layer disclosure**: the concise explicit contribution statement and detailed workflow explanation serve different purposes and remain verbatim. |

The original outer publication report SHA-256 fingerprints are `8a1dd7618b5b64e3ac2d2a4511abf413269e64922ddaae891ca8459d0e1b8225` (Markdown) and `9958007505a0cbe8594185eec8b0aa3f42d6f1a43c53073f00d8af29e7938796` (JSON). The sanitized derivatives did not reconstruct or rerun those v0.1 verification results; machine-local paths were removed. No independent v0.1.1 regression audit is claimed.

## A02 exact before/after prose ledger

Each entry records the exact replaced substring. Dated freeze and substitution records outside these present-state surfaces remain unchanged.

1. `paper/BIBLIOGRAPHY_PROVENANCE.md`

   Before:

   ```text
   No unverified bibliographic metadata remains. This is not the required future fresh priority sweep.
   ```

   After:

   ```text
   No unverified bibliographic metadata remained at this pre-publication bibliography stage. The required final fresh priority sweep was completed later, before v0.1; see the [release-gate summary](../audits/RELEASE_GATES.md).
   ```

2. `paper/CLAIM_SOURCE_MAP.md`

   Before:

   ```text
   Search outcome only, no absolute priority; final fresh sweep pending.
   ```

   After:

   ```text
   At this pre-publication source-audit stage: search outcome only, no absolute priority; the final fresh sweep was pending. It was subsequently completed before v0.1; see the [release-gate summary](../audits/RELEASE_GATES.md).
   ```

3. `provenance/SOURCE_PAPERS.md`

   Before:

   ```text
   PDFs are absent from the proposed public tree and public ZIPs.
   ```

   After:

   ```text
   PDFs are absent from the curated public tree and public ZIPs.
   ```

4. `RELEASE_AUDIT_CHANGES.md`

   Before:

   ```text
   # Release-audit wording repairs (local, unreleased)
   ```

   After:

   ```text
   # Historical pre-publication release-audit wording repairs
   ```

5. `audits/RELEASE_GATES.md`

   Before:

   ```text
   This assembly does not renew that cutoff or authorize publication.
   ```

   After:

   ```text
   At the pre-publication gate stage, this assembly did not renew that cutoff or itself authorize publication.
   ```

The manuscript PDF, paper source archive, Conjecture-1 note PDF, note Markdown/TeX, all mathematical scripts, certificates, expected results, bibliography scientific entries, frozen V3 authority, and priority positioning are byte-identical to public v0.1. All 71 displayed equations, 14 formal statements, and 14 proof blocks are unchanged. Public reproduction remains 9/9 PASS.
