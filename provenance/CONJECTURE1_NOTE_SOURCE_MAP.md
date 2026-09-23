# Conjecture-1 communication note: frozen-source map

**DERIVATIVE SCIENTIFIC CONTENT ONLY — NO NEW CLAIM**

This communication note was created against the communication-note pre-publication baseline,
commit `8f8262809efd6f270fce6cf4e3aa9c6fd38747bc`, public ZIP SHA-256
`4c8799f281dbbfd5db5349176578020d93099e0fa3017036f55234190a9279e6`,
manuscript PDF SHA-256
`c50bb26e723ce5c287c182c05e01745accd355b27e8691e6a4313e784af5657c`.
All three were verified before editing. The note Markdown, TeX, and PDF remained byte-identical through the eventual public v0.1 release at commit `4a637eaf0cd6beeaab72afca62f8069fa01793be`. No external source, private archive,
new research, new proof, strengthened statement or new calculation supplies a claim.

## Post-v0.1.2 main-branch courtesy wording sync

Current main applies only two later prose substitutions to the standalone note:
`this yields the exact contradiction` → `this yields the exact violation`, and
`The full manuscript also certifies failure throughout` →
`The full manuscript also establishes the violation throughout`.
All twelve mathematical displays and the frozen claim/source mapping below remain unchanged.
The tagged v0.1.2 release retains the earlier note bytes and PDF SHA-256
`cc6a7892b5fd3febff5d9d03cbbe75aed3c104075e6ed8925ae551b986fa39de`.
**SCIENTIFIC DELTA: NONE.**

The note is [Markdown](../docs/CONJECTURE1_COUNTEREXAMPLES.md),
[independent TeX](../docs/conjecture1_counterexamples.tex), and
[two-page PDF](../release_assets/Conjecture1_exact_counterexamples.pdf).
Display identifiers N01–N12 below denote displays in reading order; they are
mapping identifiers only, not new theorem or equation numbering in the manuscript.
The Markdown and TeX use identical mathematical display bodies and the same prose.

| Note item / mathematical content | Exact frozen manuscript source | Existing frozen certificate or data, where applicable |
|---|---|---|
| Introduction; N01: proposed hierarchy, Conjecture 1 / source Eq. (4); two separate full-rank witnesses | Introduction Eq. (1.1), `eq:source-hierarchy`; Propositions 3.1 and 3.2, plus the paragraph immediately before Theorem 3.3 | `certificates/current/RIGHT_BOUND_ONE_PAGE.md`; `certificates/prior_left/report_zh.md`, lower-side witness |
| Conventions: evolution, purity, normalized Hilbert–Schmidt seed; row-vectorized square root; both purification generators; rightmost quantity is rank-one operator complexity | Section 2.1, Eqs. (2.1)–(2.4), `eq:evolution`, `eq:general-complexity`, `eq:purification`, `eq:abbreviations`, and adjoining definitions | `certificates/current/RIGHT_BOUND_ONE_PAGE.md`, conventions |
| N02: lower witness matrices | Proposition 3.1, Eq. (3.1), `eq:left-state` | `src/frozen/left/verification_results.json`, `qutrit.H`, `qutrit.rho`; prior-left report witness |
| Lower positive spectrum; N03: square root and purity | Proposition 3.1 proof, Eq. (3.3), `eq:left-root` | Same JSON, `qutrit.sqrt_rho`, `qutrit.purity` |
| Coherence in levels 2–3, gap one, the two energy-gap measures and three-atom reduction; N04: parameters and complexities | Eq. (2.6), `eq:gap-measures`; Lemma 2.1; Proposition 3.1 proof and Eq. (3.4), `eq:left-weights` | Same JSON, `qutrit.CS.b_squared`, `qutrit.CK.b_squared`; prior-left report Eqs. (3)–(4) |
| N05: three-atom formula and range 0 < μ < 1; inline three amplitudes and index weighting | Lemma 2.1 and its proof, Eqs. (2.8)–(2.9), `eq:three-function`, `eq:three-amplitudes` | Prior-left report three-point spectral calculation |
| N06: lower finite-time values, positive gap and lower-side violation | Proposition 3.1, Eq. (3.2), `eq:left-values`; Appendix A.1, Eq. (A.1), `eq:left-probabilities` | Same JSON, `qutrit.CS.complexity_at_pi`, `qutrit.CK.complexity_at_pi`, `qutrit.gap_at_pi` |
| N07: upper witness matrices; full rank, purity 1/2 and square root | Proposition 3.2, Eq. (3.5), `eq:right-state`, and first proof sentence | `src/frozen/current/results/target1r_exact.json`, `cases[0]` named `independent_square_spectrum`; `certificates/current/RIGHT_BOUND_ONE_PAGE.md` |
| N08: mixed/purified operator spectral supports and weights; purified-vector weights and difference convolution; exact chain lengths 3 and 5 | Proposition 3.2 proof, Eq. (3.7), `eq:right-measures`; Eq. (2.7), `eq:difference-convolution`; Section 2.2 chain-length statement | Same case, `mixed.nodes`, `mixed.weights`, `purified_operator_I.nodes`, `purified_operator_I.weights`; `RIGHT_BOUND_DETAILS.md`, channel A |
| N09: real orthonormal-polynomial spectral prescription and index-weighted complexity; orthonormalizing monomials | Section 2.2 and Eq. (2.5), `eq:spectral-formula`; Eq. (2.2), `eq:general-complexity`; existing scalar weighted-polynomial method | `certificates/current/RIGHT_BOUND_DETAILS.md`, channel A; exact case `polynomials`, `norms` |
| Squared Lanczos coefficients and zero diagonals; N10: full rational probabilities at π/3; normalization and index-weighted sums | Appendix A.1, Eqs. (A.2)–(A.3), `eq:right-lanczos`, `eq:right-probabilities`, and following paragraph | Same exact case, both branches' `b_squared`, `a`, `probabilities`; direct-matrix certificate comparisons retained unchanged |
| N11: upper finite-time values, positive gap and upper-side violation | Proposition 3.2, Eq. (3.6), `eq:right-values` | Same exact case, both branches' `complexity` and the certified gap; `RIGHT_BOUND_ONE_PAGE.md` |
| N12: short-time coefficients and O(t⁴) remainders; certified interval 0 < t < 1/2704 | Proposition 3.2, Eqs. (3.8)–(3.9), `eq:right-curvatures`, `eq:right-interval`; Appendix B.1 remainder bound | `certificates/current/RIGHT_BOUND_ONE_PAGE.md`, short-time certificate; `RIGHT_BOUND_DETAILS.md` |
| Final scope: both states strictly full rank, separate witnesses; every qubit density matrix, every time-independent Hermitian Hamiltonian and every real time; physical dimension 3 minimal for failure of either side | Propositions 3.1–3.2; exact scope of Theorem 3.3, `thm:qubit`, and preceding separation paragraph | Theorem 3.3 is the controlling scope statement; the note does not extend its hypotheses or conclusion |

The last sentence identifying the full manuscript and accompanying materials is
provenance, not a mathematical assertion. No Conjecture-2, factor-two, perturbation,
new minimality, generality, novelty or priority claim is introduced. Neither witness
is described as violating both inequalities. The note carries only Dehao Lin's
human author line and refers to the full manuscript's existing AI disclosure.

## Traceability verification

All twelve mathematical displays, all inline formulas and all mathematical prose
were checked against the mapped frozen text/data. Witness entries, fractions,
supports, ordered weights, ordered probabilities, parameter ranges, quantifiers
and directions of inequality retain their frozen values. The full probability
vectors and spectral prescription are included for a check from the note alone.
The two representations share the same mathematical and prose blocks. This is
a derivative-content correspondence check, not a fresh mathematical audit.

**Derivative-content audit: PASS.**

## Standalone build and license

Copy only `docs/conjecture1_counterexamples.tex` into an empty directory and run
`tectonic conjecture1_counterexamples.tex`. With a populated TeX cache,
`tectonic --untrusted --only-cached conjecture1_counterexamples.tex` builds offline.
No bibliography file, repository import, certificate, custom style or private
archive is a build input. The clean build and two-page visual inspection are
recorded in `release_verification/CONJECTURE1_NOTE_CHECK.json`.

The original communication note is within the existing original-documentation
CC BY 4.0 grant; existing third-party exclusions in LICENSING.md remain unchanged.
No third-party source PDF is included or relicensed.

## Exact source fingerprints from the exclusive baseline

The following source files are unchanged in this micro-refreeze.

| Frozen public source path | SHA-256 |
|---|---|
| `paper/sections/01_introduction.tex` | `ee013ae13df5f4b9d5f2b22fcfb524f51c3f4673641047ffc1b9a5955815d87d` |
| `paper/sections/02_framework.tex` | `a6e371cbd0b91eceb6b60a2827a9b6e7a9972a09e50c88df700c01f6c3b31f25` |
| `paper/sections/03_hierarchy.tex` | `b592b8bd4311a509133e469c868ec829377da18268e415eddf0b46053ecd6a4d` |
| `paper/sections/appendix_certificates.tex` | `5ef63b9387ad6b1505d2c1cdf1cde947faa79b55d70837b5130f17e056dc5a11` |
| `paper/sections/appendix_bounds.tex` | `f722fcf210f2d460950c9ac5c7c6b94fd13d3609032eacf221c4c49ea8fb84cf` |
| `certificates/prior_left/report_zh.md` | `bf64eaa977f80068cdeae658c1f9c27df7cbdc91d2558e740dcfea72425f7726` |
| `certificates/current/RIGHT_BOUND_ONE_PAGE.md` | `221c23dfd7aa251b9faf1fad6c85bb8d01966f4818b7ab7ca89835ace4902064` |
| `certificates/current/RIGHT_BOUND_DETAILS.md` | `9da70a773092d6df9cf2eee45903a4f54c2235bbdc468f5163a61ceb7a36ccf4` |
| `src/frozen/left/verification_results.json` | `1999c642c3af34b77a8b05c75d5125403d380ec4dc0c752f1c9d822a06460146` |
| `src/frozen/current/results/target1r_exact.json` | `e0ce6cdc2254f556a1095c499d593229c2b30adbb7cb674cae56c3b72d9ac364` |
