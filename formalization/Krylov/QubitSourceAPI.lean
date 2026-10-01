import Krylov.QubitParameterization
import Krylov.CertifiedMatrixGS

/-! Identification of the qubit's explicit padded Lanczos chains with the
literal generic Gram--Schmidt source complexity. -/
namespace Krylov.QubitSourceAPI
open Matrix OperatorBridge ConcreteChains UnitaryCovariance UniversalQubit PhysicalQubit
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def paddedPolynomial (b μ : ℝ) : Fin 3 → Polynomial ℂ :=
  ![1, Polynomial.C ((b:ℂ)⁻¹)*Polynomial.X,
    Polynomial.C (((b:ℂ)^2)⁻¹)*Polynomial.X^2-Polynomial.C (μ:ℂ)]

theorem paddedPolynomial_degree (b μ : ℝ) (hb : b ≠ 0) (i : Fin 3) :
    (paddedPolynomial b μ i).degree = (i.val : WithBot ℕ) := by
  have hb' : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  fin_cases i
  · simp [paddedPolynomial]
  · exact Polynomial.degree_C_mul_X (inv_ne_zero hb')
  · change (Polynomial.C (((b:ℂ)^2)⁻¹)*Polynomial.X^2-Polynomial.C (μ:ℂ)).degree = 2
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · exact Polynomial.degree_C_mul_X_pow 2 (inv_ne_zero (pow_ne_zero 2 hb'))
    · rw [Polynomial.degree_C_mul_X_pow 2 (inv_ne_zero (pow_ne_zero 2 hb'))]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)

theorem paddedPolynomial_evaluation {H A : Operator ι} {v : Fin 3 → Operator ι}
    {μ s b : ℝ} (h : PaddedLanczos H A v μ s b) (hb : b ≠ 0) (i : Fin 3) :
    (Polynomial.aeval (matrixCommutator H)) (paddedPolynomial b μ i) A = v i := by
  have hb' : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have h0 : matrixCommutator H A = (b:ℂ) • v 1 := by rw [← h.seed]; exact h.step_zero
  have h2 : ((matrixCommutator H)^2) A =
      (b:ℂ)^2 • v 2 + ((b:ℂ)^2*(μ:ℂ)) • A := by
    simp only [pow_two,Module.End.mul_apply,h0,map_smul,h.step_one,smul_add,smul_smul,h.seed]
    simp only [mul_assoc]
  fin_cases i
  · simpa [paddedPolynomial] using h.seed.symm
  · simp [paddedPolynomial,Module.End.mul_apply,h0,hb']
    change (b:ℂ) • ((b:ℂ)⁻¹ • v 1) = v 1
    rw [smul_smul,mul_inv_cancel₀ hb',one_smul]
  · simp [paddedPolynomial,Module.End.mul_apply,h2,smul_add,smul_smul,hb',
      ← mul_assoc]

theorem padded_orthogonal {H A : Operator ι} {v : Fin 3 → Operator ι}
    {μ s b : ℝ} (h : PaddedLanczos H A v μ s b) :
    Pairwise (fun i j => hsInner (v i) (v j) = 0) := by
  intro i j hij
  simpa [hij] using h.gram i j

theorem padded_power_mem {H A : Operator ι} {v : Fin 3 → Operator ι}
    {μ s b : ℝ} (h : PaddedLanczos H A v μ s b) (k : ℕ) :
    ((matrixCommutator H)^k) A ∈ Submodule.span ℂ (Set.range v) := by
  rw [h.complete]
  exact Submodule.subset_span ⟨k,rfl⟩

theorem zero_mass_stationary {H A : Operator ι} {v : Fin 3 → Operator ι}
    {s b : ℝ} (h : PaddedLanczos H A v 0 s b) : matrixCommutator H A = 0 := by
  have h0 := h.step_zero
  rw [h.seed,h.zero_mass_padding.1,smul_zero] at h0
  exact h0


/-- A zero frequency in a complete padded chain forces its mass to be zero;
this derives termination from the certificate instead of assuming it. -/
theorem zero_frequency_mass {H A : Operator ι} {v : Fin 3 → Operator ι}
    {μ s : ℝ} (h : PaddedLanczos H A v μ s 0) : μ=0 := by
  have hz : matrixCommutator H A=0 := by
    have hs := h.step_zero
    simpa [h.seed] using hs
  have hs := (stationary_certificate H A s h.scale_pos h.seed_norm hz).cyclic_dimension
  have hh := h.cyclic_dimension
  by_contra hm
  simp only [hm,if_false] at hh
  simp only [if_pos rfl] at hs
  have he := hs.symm.trans hh
  norm_num at he

lemma commuting_actual_zero (H A : Operator ι) (hc : H*A-A*H=0) (t : ℝ) :
    PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian H)
      (PhysicalCurvatureNecessary.normalizedSeed A) t=0 := by
  apply PureShortTime.actual_stationary _ _ 0
  simp [PhysicalCurvatureNecessary.normalizedSeed,map_smul,
    PerturbedDynamics.liouvillian_rowVectorize,hc]

/-- The certificate's finite weighted probability sum equals the literal
normalized GS operator complexity. Both zero mass and zero frequency are
included; a negative frequency is handled by polynomial leading phases. -/
theorem padded_actual_eq {H A : Operator ι} {v : Fin 3 → Operator ι}
    {μ s b : ℝ} (hH : H.IsHermitian) (h : PaddedLanczos H A v μ s b) (t : ℝ) :
    PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian H)
      (PhysicalCurvatureNecessary.normalizedSeed A) t = matrixComplexity H A v t := by
  by_cases hb : b=0
  · subst b
    have hm := zero_frequency_mass h
    subst μ
    have hz := zero_mass_stationary h
    have hc : H*A-A*H=0 := hz
    rw [commuting_actual_zero H A hc t]
    obtain ⟨h1,h2⟩ := h.zero_mass_padding
    simp [matrixComplexity,Fin.sum_univ_succ,h1,h2,matrixProbability_zero]
  · exact CertifiedMatrixGS.actual_eq_matrix_sum H A hH h.seed_nonzero v
      (paddedPolynomial b μ) (fun i => (paddedPolynomial_evaluation h hb i).symm)
      (paddedPolynomial_degree b μ hb) (padded_orthogonal h) h.complete t

/-- Actual source U*-branch spread equals the previously computed qubit chain. -/
theorem source_spread_eq {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (t : ℝ) :
    PurificationBranches.spread (PurificationBranches.generatorU H)
      (PurificationBranches.seed hρ) t = UniversalQubit.spread hH hρ t := by
  rw [MatrixGSBridge.spread_eq_normalized hH hρ htr t]
  exact padded_actual_eq hH (spread_chain_certificate hH hρ htr) t

/-- Actual source normalized mixed-density GS complexity equals its qubit chain. -/
theorem source_mixed_eq {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (t : ℝ) :
    PhysicalCurvatureNecessary.mixedComplexity H ρ t = UniversalQubit.mixed hH ρ t :=
  padded_actual_eq hH (mixed_chain_certificate hH hρ htr) t

/-- Actual source I-branch pure-operator GS complexity equals its qubit chain. -/
theorem source_purified_eq {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (t : ℝ) :
    PurificationBranches.pureOperator (PurificationBranches.generatorI H)
      (PurificationBranches.seed hρ) t = UniversalQubit.purified hH hρ t := by
  rw [MatrixGSBridge.pure_eq_normalized hH hρ htr t]
  have hL : (PurifiedCovariance.lift H).IsHermitian := by
    change (PurifiedCovariance.lift H)ᴴ=PurifiedCovariance.lift H
    rw [PurifiedCovariance.lift_adjoint,hH.eq]
  have he := padded_actual_eq hL (purified_chain_certificate hH hρ htr) t
  simpa only [PurificationBranches.generatorI_eq_kronecker,PurifiedCovariance.lift]
    using he

/-- Literal source eq:qubit-mus, now using the same GS-based quantities as
PurificationBranches and the mixed-density curvature API. -/
theorem source_formulas {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (t : ℝ) :
    let q := coordinateDensity_posSemidef hH hρ
    let z := QubitParameterization.contrast q
    let c := QubitParameterization.angleParameter q
    PurificationBranches.spread (PurificationBranches.generatorU H)
      (PurificationBranches.seed hρ) t = Qubit.threeAtom (Qubit.muS z c) (energyGap hH*t) ∧
    PhysicalCurvatureNecessary.mixedComplexity H ρ t = Qubit.threeAtom (Qubit.muK z c) (energyGap hH*t) ∧
    PurificationBranches.pureOperator (PurificationBranches.generatorI H)
      (PurificationBranches.seed hρ) t = Qubit.threeAtom (Qubit.muI z c) (energyGap hH*t) := by
  dsimp only
  obtain ⟨hS,hK,hI⟩ := QubitParameterization.energy_basis_coefficients hH hρ htr
  rw [source_spread_eq hH hρ htr,source_mixed_eq hH hρ htr,source_purified_eq hH hρ htr,
    spread_eq hH hρ htr,mixed_eq hH hρ htr,purified_eq hH hρ htr,hS,hK,hI]
  exact ⟨rfl,rfl,rfl⟩

/-- Universal qubit hierarchy in the literal generic source API, for every
PSD trace-one density, every Hermitian Hamiltonian, and every real time. -/
theorem source_hierarchy {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (t : ℝ) :
    PurificationBranches.spread (PurificationBranches.generatorU H)
      (PurificationBranches.seed hρ) t ≤ PhysicalCurvatureNecessary.mixedComplexity H ρ t ∧
    PhysicalCurvatureNecessary.mixedComplexity H ρ t ≤
      PurificationBranches.pureOperator (PurificationBranches.generatorI H)
        (PurificationBranches.seed hρ) t := by
  rw [source_spread_eq hH hρ htr,source_mixed_eq hH hρ htr,source_purified_eq hH hρ htr]
  exact UniversalQubit.hierarchy hH hρ htr t

/-- The continuous ratio extension agrees with the literal source GS ratio
at every nonrecurrence time. -/
theorem source_ratio_eq {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hc : H*ρ-ρ*H ≠ 0) {t : ℝ}
    (ht : Real.sin (energyGap hH*t/2) ≠ 0) :
    PhysicalQubitCV.extendedRatio hH hρ t =
      PurificationBranches.spread (PurificationBranches.generatorU H)
        (PurificationBranches.seed hρ) t / PhysicalCurvatureNecessary.mixedComplexity H ρ t ∧
    PhysicalQubitCV.extendedReciprocal hH hρ t =
      PhysicalCurvatureNecessary.mixedComplexity H ρ t /
        PurificationBranches.spread (PurificationBranches.generatorU H) (PurificationBranches.seed hρ) t ∧
    PhysicalQubitCV.extendedPurityRatio hH hρ t = PhysicalQubit.purity ρ *
      (PhysicalCurvatureNecessary.mixedComplexity H ρ t /
        PurificationBranches.spread (PurificationBranches.generatorU H) (PurificationBranches.seed hρ) t) := by
  rw [source_spread_eq hH hρ htr,source_mixed_eq hH hρ htr]
  have hn := PhysicalQubitCV.nonstationary_of_commutator_ne hH hρ htr hc
  exact ⟨PhysicalQubitCV.ratio_eq_actual hH hρ htr hn ht,
    PhysicalQubitCV.reciprocal_eq_actual hH hρ htr hn ht,
    PhysicalQubitCV.purityRatio_eq_actual hH hρ htr hn ht⟩

/-- Source CV bound, together with continuity of each actual source-ratio
extension. The preceding theorem identifies each extension off recurrence. -/
theorem source_cv {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hc : H*ρ-ρ*H ≠ 0)
    (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] :
    Continuous (PhysicalQubitCV.extendedRatio hH hρ) ∧
    Continuous (PhysicalQubitCV.extendedReciprocal hH hρ) ∧
    Continuous (PhysicalQubitCV.extendedPurityRatio hH hρ) ∧
    RestrictedCV.coefficientVariation (PhysicalQubitCV.extendedRatio hH hρ) ν ≤
      (RestrictedCV.kappaStar-1)/(2*Real.sqrt RestrictedCV.kappaStar) ∧
    RestrictedCV.coefficientVariation (PhysicalQubitCV.extendedReciprocal hH hρ) ν ≤
      (RestrictedCV.kappaStar-1)/(2*Real.sqrt RestrictedCV.kappaStar) ∧
    RestrictedCV.coefficientVariation (PhysicalQubitCV.extendedPurityRatio hH hρ) ν ≤
      (RestrictedCV.kappaStar-1)/(2*Real.sqrt RestrictedCV.kappaStar) := by
  have hn := PhysicalQubitCV.nonstationary_of_commutator_ne hH hρ htr hc
  exact ⟨PhysicalQubitCV.continuous_extendedRatio hH hρ htr,
    PhysicalQubitCV.continuous_extendedReciprocal hH hρ htr hn,
    PhysicalQubitCV.continuous_extendedPurityRatio hH hρ htr hn,
    PhysicalQubitCV.physical_qubit_cv_of_commutator_ne hH hρ htr hc ν⟩

lemma subsingleton_commutator [Subsingleton ι] (H A : Operator ι) : H*A-A*H=0 := by
  apply sub_eq_zero.mpr
  ext i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Subsingleton.elim k i,Subsingleton.elim j i]
  exact mul_comm _ _

/-- Every literal source complexity vanishes in physical dimension one,
including the I-purified operator, whose ambient tensor index is also singleton. -/
theorem dimension_one_zero {H ρ : Operator (Fin 1)} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (t : ℝ) :
    PurificationBranches.spread (PurificationBranches.generatorU H) (PurificationBranches.seed hρ) t=0 ∧
    PhysicalCurvatureNecessary.mixedComplexity H ρ t=0 ∧
    PurificationBranches.pureOperator (PurificationBranches.generatorI H) (PurificationBranches.seed hρ) t=0 := by
  rw [MatrixGSBridge.spread_eq_normalized hH hρ htr,MatrixGSBridge.pure_eq_normalized hH hρ htr]
  exact ⟨commuting_actual_zero _ _ (subsingleton_commutator _ _) t,
    commuting_actual_zero _ _ (subsingleton_commutator _ _) t,
    commuting_actual_zero _ _ (subsingleton_commutator _ _) t⟩

end
end Krylov.QubitSourceAPI
