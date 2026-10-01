# Source correspondence and coverage — v4

Authoritative source: `ea43fcc3fc033d7c6ce0887d5747c05868879508`. This replaces v2's insufficient API correspondence. The precise inventory is `GAP_MANIFEST.md` plus `SOURCE_CLAIM_LEDGER.tsv`; current validation state is `SOURCE.json`.

## Generic source definitions

The source quantities retain their existing definitions:

- `FactorTwoFinite.complexity`: weighted normalized Gram–Schmidt of the actual power sequence
- `PhysicalCurvatureNecessary.mixedComplexity`: commutator dynamics of the density normalized by its HS norm
- `PurificationBranches.spread (generatorU H) (seed hρ)`: canonical-root U* purification spread
- `PurificationBranches.pureOperator (generatorI H) (seed hρ)`: canonical I-purification rank-one operator complexity

`CertifiedGS` proves triangular/polynomial uniqueness, arbitrary leading coefficient phase, actual termination and zero padding. `MatrixGSBridge`, `CertifiedMatrixGS` and `GSUnitaryTransport` prove normalization, true exponentials, row vectorization and unitary transport. No auxiliary chain is declared to be the source definition.

## Headline source statements

| Source | Final entry point |
|---|---|
| lem:three | `ThreeAtomSourceAPI.state_complexity_eq`, `actual_complexity_eq`; μ∈[0,1], every real frequency and time |
| prop:left | `WitnessSourceAPI.prop_left`; canonical source spread and mixed quantities at π |
| prop:right | `WitnessSourceAPI.prop_right`, `right_interval`; original matrices, exact π/3 values and entire source interval |
| thm:qubit | `QubitSourceAPI.source_hierarchy`, `SourceProse.literal_qubit_formulas` |
| d=3 minimality | `SourceProse.minimal_physical_dimension`; separate IsLeast statements for both sides, same API |
| thm:factor and sharpness | unchanged `FactorTwoTheorem.finite_dimensional_factor_two`, `FactorTwoSharpnessGS.exact_saturation`, `universal_multiplier_le_two` |
| cor:branches | unchanged `PurificationBranches.K_I_ge_two_S_I`, `K_U_ge_two_S_U` |
| thm:main-ratio | `CanonicalFamilySource.main_continued_cv_lower`, `main_continued_cv_unbounded`, `main_continued_finite_witness` |
| thm:reciprocal | `CanonicalFamilySource.reciprocal_continued_cv_lower`, `reciprocal_continued_cv_unbounded`, `reciprocal_continued_finite_witness`, `reciprocal_scaled_continued_finite_witness` |
| thm:purity | `FamilySourceAPI.fixed_purity`, `fixed_uniform_bounds`, `fixed_uniformly_diverges`, `fixed_periodMean_unbounded`, both reciprocal uniform-small theorems |
| prop:qubit-cv | `SourceProse.source_cv_with_identification`; literal ratio agreement, positivity, continuity and arbitrary-probability-measure bounds in one theorem |
| prop:unbounded-left | `CanonicalFamilySource.qutrit_all_time_strict`, `qutrit_asymptotic`, `qutrit_no_positive_multiplier` |
| prop:robust | `PerturbedSourceAPI.robust_qutrit_witness`, `finite_certificate`, `cubic_certificate` |
| lem:return / cor:return-comparison | unchanged `ActualReturnBounds.actual_return_bounds`, `PhysicalReturnComparison.physical_return_comparison` |
| Curvature necessity | unchanged `PhysicalCurvatureNecessary.hierarchy_forces_curvature` |

Family functions are transparent instantiations of existing `actualComplexity` / `mixedComplexity`, not new complexity definitions. Their admissible-parameter `*_canonical` equalities prove the explicit roots equal the canonical purification roots.

## Supporting source displays and prose

- `SourceProse.literal_qubit_formulas`, `literal_qubit_range_parameters`, `nonstationary_angular_parameters` connect actual eigenvalues and actual basis rotation to z/c and y/h, including endpoints
- `RightWitnessCurvature.source_expansions` is genuinely two-sided at `nhds 0`; `literal_curvatures` gives 225/169 and 221/169 individually
- Both curvature violations are explicit in `CurvatureDisplayRepair.left_curvature_violation` and `RightWitnessCurvature.right_curvature_violation`
- `WitnessProbabilityAPI` proves every displayed witness probability as an actual normalized-GS degree probability; canonical-root spread is represented by its equivalent commutator action, and the purified table by the original rank-one seed
- `LanczosSourceAPI` gives actual normalized-GS coupling-square tables and zero diagonals in energy coordinates; `GSUnitaryTransport` proves unitary correspondence
- `TerminalSourcePolynomials` gives the original-basis terminal annihilators; `WitnessChainLengths` gives exact actual GS lengths and termination
- `FamilyEigenvalues` gives characteristic polynomial factorizations and root multisets, including multiplicities, for the source eigenvalue lists
- `SourceMomentBounds` exports the individually displayed mean, peak-window and second-moment inequalities for actual continuous source ratios
- `SourceRecurrenceSets` states exact 2πℤ zero sets and nonrecurrence at π
- `SourceProse.cv_constant_decimal` proves the exact rational enclosure 0.13756338852–0.13756338853; `stationary_mixed_nonstationary_purification` supplies the source's explicit stationary-density distinction

## Recurrence and integration

`FamilySourceAPI` gives continuous positive extensions agreeing with the literal GS quotients off recurrence, finite positive punctured two-sided limits at every recurrence, exact periodicity and finite first/second moments. Pointwise continuity is not inferred merely from null-set invariance. The existing valid countable-null-set CV proof remains, with separate equality theorems transporting it to the continuous extensions. Qubit arbitrary probability measures, including atoms at recurrences, use the actual continuous extension.

## Equivalent proof routes and exclusions

Finite atomic integrals are represented by exact finite sums. The unperturbed interval and qubit monotonicity/optimization use alternative polynomial/factorization arguments; replaced intermediate norm/calculus steps are not claimed as standalone formalized lemmas. Explicit source results, constants, domains and physical definitions remain unchanged.

Quoted conjectures, history, provenance, priority/novelty and non-authoritative archives are excluded. No CV-attainment claim, all-interpretations Conjecture-2 refutation, or three-dimensional temporal-CV minimality is introduced. See `REMAINING_RETAINED_STATEMENTS.md` for final residual status.

## V4 release gate and subsidiary derivations

The canonical endpoint transport section of `GAP_MANIFEST.md` specifies exact function equalities for each group and how every subsidiary v3 display is mechanically transported. Final temporal roots include continuous, scaled, finite and unbounded declarations. The fixed-purity endpoints preserve the full parameter interval; the qutrit endpoint preserves every real m>=4 and all nonrecurrence times. The delta-general bridges hold for every real delta/time.

`SemanticDependencies.lean` traverses proof values only and requires each final family root to reach its own canonical spread bridge, the appropriate `CertifiedFamilyGS` bridge, generic GS uniqueness, and `MatrixGSBridge.spread_eq_normalized`. Perturbed roots instead require both delta-general bridges, the genuine pure-operator transport and actual-GS expectation bridge. This tailored gate does not demand irrelevant certified-chain mathematics of perturbative estimates. Runtime matrix: `verification/v4-required-bridge-matrix.json`.

F-16 is retained/category B in the 128-row ledger; its exact derivation is recorded there and in the gap manifest. All 94 v3 proof modules must remain byte-identical. Counts and logs are evidence only after the corresponding gate has run; `RELEASE_HARDENING_V4.md` distinguishes local and independent CI execution.

## Executed v4 evidence

Independent GitHub Actions run 36866846382 passed a zero-project-olean start, 97-module build, module-provenance audit, all 88 required value-only paths for 22 final roots, four negative controls, source-reference comparison, ledger/coverage checks and before/after proof hashes. The current 99 proof-source files match the downloaded passing artifact exactly. The logical axiom union is exactly propext, Quot.sound and Classical.choice. The immutable run and artifact identities are recorded in `SOURCE.json`. See `HISTORY.md` for review scope and limitations; the final publication layout receives a separate CI run.
