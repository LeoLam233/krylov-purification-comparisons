# Exact limits of Krylov-complexity comparisons under purification

Public v0.1.1 reproducibility package for the [release-audited manuscript](paper/main.pdf),
using the authoritative V3 scientific freeze. The manuscript and Conjecture-1 note are byte-identical to v0.1.

**PUBLIC v0.1.1 RELEASED — 2026-09-24**

Repository: [https://github.com/LeoLam233/krylov-purification-comparisons](https://github.com/LeoLam233/krylov-purification-comparisons)  
Release: [v0.1.1](https://github.com/LeoLam233/krylov-purification-comparisons/releases/tag/v0.1.1) ([v0.1 history](https://github.com/LeoLam233/krylov-purification-comparisons/releases/tag/v0.1)).
Documentation/provenance patch: [hostile-audit closure](audits/V0_1_1_HOSTILE_AUDIT_CLOSURE.md); v0.1 publication evidence: [public-safe report](release_verification/PUBLICATION_VERIFICATION_REPORT.md) and [JSON](release_verification/PUBLICATION_VERIFICATION_REPORT.json).

Author: **Dehao Lin**. Affiliation: School of Physics, Sun Yat-sen University,
Guangzhou, China. No ORCID; no specific funding; no acknowledgements.
Two recorded prose repairs and the rebuilt assets are described in [RELEASE_AUDIT_CHANGES.md](RELEASE_AUDIT_CHANGES.md).

The source problem is the comparison of normalized Hilbert--Schmidt operator
Krylov complexity and purification spread complexity in Das and Mori,
*Krylov complexity of purification*, arXiv:2408.00826v4 / PRL 136, 030201.
See [source metadata and versioned links](provenance/SOURCE_PAPERS.md).

With the manuscript's notation, source Eq. (4) is S_U*(t) <= C_M(t) <= K_I(t).
Its two sides have **separate exact full-rank qutrit counterexamples**:
the left gap S_U* - C_M is 4192/74529 at t=pi, and the right gap C_M - K_I
is 1600683/39299936 at t=pi/3. Both inequalities hold for every qubit density
matrix, every time-independent Hermitian qubit Hamiltonian and every real time,
including stationary and degenerate cases. Physical dimension three is minimal
for failure of either side.

The factor-two inequality C_K >= 2 C_S holds for finite-dimensional normalized
pure seeds and Hermitian generators at all real times, and applies separately
to both purification branches. It follows from existing tensor-product
superadditivity by Murugan and van Zyl (arXiv:2601.08723v1); it is not presented
as a new headline result. The manuscript retains only this finite-dimensional scope.

For the qualitative, unquantified Conjecture 2, the retained results rule out
explicit universal concentration and purity-only-control formulations. At fixed
d=4 and H, two distinct full-rank families have unbounded full-period CV(r) and
CV(q)=CV(Pq), respectively, where r=S_U*/C_M and q=1/r. A third family at fixed
d=4, H and purity P=1/2 has unbounded r and its period mean. Ratios use removable
continuation at common recurrences. These statements do not refute every reading
of the qualitative conjecture or the source's sample-specific numerical observations.
Exact hypotheses, parameter ranges and unchanged V3 constants are in [CLAIMS.md](CLAIMS.md)
and the [manuscript claim map](paper/CLAIM_SOURCE_MAP.md).

[Quick verification of Conjecture 1](docs/CONJECTURE1_COUNTEREXAMPLES.md) ([standalone PDF](release_assets/Conjecture1_exact_counterexamples.pdf)).

## Reproduce and build

Use Python 3.11 or newer and the frozen dependency pins:

```text
python -m pip install -r requirements.txt
python scripts/verify_assets.py
python scripts/reproduce.py
python scripts/build_paper.py --engine tectonic
```

The default replay verifies and extracts a curated **byte-identical file view**
of V3's mathematical verifiers into a disposable directory. It is not a replacement
authoritative freeze. The full local archive replay additionally verifies the
private originals and extracts the original mathematical ZIPs:

```text
python scripts/reproduce.py --private-assets ../Krylov_Private_Assets
python scripts/check_paper.py --private-assets ../Krylov_Private_Assets
```

Replays fail on mismatches and write machine-readable JSON plus logs under `.local/`.
Original scripts are unchanged. Exact-only, mixed legacy, and non-rigorous numerical
jobs are labeled separately; floating-point agreement is not a proof.
See [REPRODUCIBILITY.md](REPRODUCIBILITY.md) for offline builds and result semantics.

## AI contribution and research workflow

**AI contribution statement.** AI systems played the primary and largest role in the scientific work reported here. They identified the source paper as a research target, developed the attacks on its conjectures, constructed the counterexamples, derived the proofs and auxiliary results, produced and checked the computational certificates, and assisted in the adversarial audits, clean-room reproductions, and preparation of the manuscript. Dehao Lin designed and supervised the overall research workflow, made the project and release decisions, reviewed the resulting artifacts, and assumes responsibility for the final manuscript.

The project used an AI-centered theoretical-physics workflow designed and supervised
by Dehao Lin. AI systems autonomously searched for research targets. The workflow
identified Das and Mori's *Krylov complexity of purification* and its conjectures.
AI systems played the primary scientific role in attacking those conjectures,
constructing the exact counterexamples, deriving proofs and auxiliary results,
writing and executing verification code, and carrying out hostile audits and
clean-room reproductions. They also assisted with manuscript and repository preparation.
The human role included workflow design and refinement, standards of evidence,
supervision, review, and final release decisions. AI-to-AI agreement is not presented
as independent human peer review.

## Evidence and status

Current certification consists of independent **AI hostile audits and AI clean-room
reproductions**. It is not human peer review or independent human/expert validation.
The clean rooms reproduce seven supplied targets, not independent discovery of those
witnesses or every V3 byproduct. See [audits](audits/README.md) and [clean-room summaries](clean_room/README.md).

The supplied 2026-09-22 prior-art audit reported no matching public result for the
retained hierarchy-counterexample and quantified ratio no-go claims. That dated
search outcome is not an absolute priority claim. The attached final sweep records
**PASS — PRIORITY SWEEP ONLY**, with a public-retrieval cutoff of 2026-09-23 09:25:29 UTC.
No matching public prior result was found in that finite sweep; absolute priority is
not claimed. Its qualifications and the frozen novelty positioning are preserved;
see [the release-gate summary](audits/RELEASE_GATES.md). No new search was performed in this assembly.

The scientific content remains that of audited RC1. The two earlier release-audit
prose repairs are preserved. This assembly changes only approved metadata, disclosure,
licensing and packaging; see [the final delta audit](FINAL_SCIENTIFIC_DELTA_AUDIT.md)
and [the exact file-change inventory](FINAL_FILE_CHANGES.md).

## Archival boundary and licenses

**Archival boundary.** This public repository is a curated release view of a larger
frozen research archive. The internal archive contains historical freezes, raw audit
and clean-room packages, workflow handoffs, third-party source PDFs, and other
provenance material. Those materials are retained separately and are not all
redistributed here, either because they are internal archival records or because
redistribution rights are not assumed. Publicly relevant results, exact certificates,
reproduction scripts, scope statements, and cryptographic fingerprints are included
in this repository.

Original code is under the [MIT License](LICENSE). Original manuscript and
documentation are under [CC BY 4.0](LICENSE-CC-BY-4.0.md). Third-party material is
excluded from these grants; see [the licensing scope](LICENSING.md).
Use [CITATION.cff](CITATION.cff) for the supplied author and citation metadata.
See [the public/private boundary](PUBLIC_PRIVATE_BOUNDARY.md),
[inventory](REPOSITORY_INVENTORY.md), [asset map](RELEASE_ASSET_MAP.md),
[path notes](docs/STAGING_PATHS.md), and [release notes](RELEASE_NOTES.md).
