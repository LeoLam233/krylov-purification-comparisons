import Krylov.LanczosSourceAPI
import Krylov.ActualReturnBounds

/-! Exact termination lengths of the source's right-hand witnesses, measured
by the nonzero indices of their actual normalized Gram–Schmidt chains. -/
namespace Krylov.WitnessChainLengths
open Matrix OperatorBridge ConcreteChains UnitaryCovariance MatrixGSBridge
open PhysicalCurvatureNecessary PerturbedDynamics ActualReturnBounds FactorTwoFinite
open WitnessSourceAPI
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalized_cyclic_dimension (H A : Operator ι) (hA : A ≠ 0) :
    chainLength (PerturbedDynamics.liouvillian H) (normalizedSeed A) =
      Module.finrank ℂ (ConcreteChains.cyclicSpan (FactorTwo.commutator H) A) := by
  rw [length_eq_cyclic_finrank]
  let c : ℂ := (‖FactorTwo.rowVectorize A‖⁻¹ : ℝ)
  have hc : c ≠ 0 := by
    have hn : ‖FactorTwo.rowVectorize A‖ ≠ 0 := by
      intro hz
      apply hA
      exact FactorTwo.rowVectorize.injective (by simpa using norm_eq_zero.mp hz)
    change ((‖FactorTwo.rowVectorize A‖⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast inv_ne_zero hn
  have hs : FactorTwoFinite.cyclicSpan
      (powerSequence (PerturbedDynamics.liouvillian H) (normalizedSeed A)) =
      (ConcreteChains.cyclicSpan (FactorTwo.commutator H) A).map
        FactorTwo.rowVectorize.toLinearMap := by
    unfold FactorTwoFinite.cyclicSpan ConcreteChains.cyclicSpan
    rw [Submodule.map_span, ← Set.range_comp]
    have hf (n : ℕ) : powerSequence (PerturbedDynamics.liouvillian H)
        (normalizedSeed A) n = c • FactorTwo.rowVectorize ((FactorTwo.commutator H ^ n) A) := by
      simp [powerSequence,normalizedSeed,map_smul,liouvillian_power_rowVectorize,c]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨n,rfl⟩
      rw [hf]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨n,rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨n,rfl⟩
      have hm := Submodule.smul_mem
        (Submodule.span ℂ (Set.range (powerSequence
          (PerturbedDynamics.liouvillian H) (normalizedSeed A)))) c⁻¹
        (Submodule.subset_span (Set.mem_range_self n))
      simpa only [hf,smul_smul,inv_mul_cancel₀ hc,one_smul,Function.comp_apply] using hm
  rw [hs,LinearEquiv.finrank_map_eq]

lemma gs_card_isometry {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : E ≃ₗᵢ[ℂ] F) (f : ℕ → E) :
    Fintype.card (GSIndex (fun n => T (f n))) = Fintype.card (GSIndex f) := by
  let e : GSIndex f ≃ GSIndex (fun n => T (f n)) :=
    { toFun := fun k => ⟨k.val, by
        change gramSchmidtNormed ℂ (fun n => T (f n)) k.val ≠ 0
        rw [← PhysicalSpectralPolynomials.isometry_gramSchmidtNormed]
        exact fun hz => k.property (T.injective (by simpa using hz))⟩
      invFun := fun k => ⟨k.val, by
        change gramSchmidtNormed ℂ f k.val ≠ 0
        intro hz
        apply k.property
        rw [← PhysicalSpectralPolynomials.isometry_gramSchmidtNormed,hz,map_zero]⟩
      left_inv := fun k => by apply Subtype.ext; rfl
      right_inv := fun k => by apply Subtype.ext; rfl }
  exact (Fintype.card_congr e).symm

lemma length_changeBasis (Q H A : Operator ι) (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1) :
    chainLength (PerturbedDynamics.liouvillian (changeBasis Q H))
      (normalizedSeed (changeBasis Q A)) =
      chainLength (PerturbedDynamics.liouvillian H) (normalizedSeed A) := by
  unfold chainLength
  rw [funext (GSUnitaryTransport.normalized_power_change Q H A hQ hQ')]
  exact gs_card_isometry _ _

lemma later_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (L : E →L[ℂ] E) (v : E) (n : ℕ)
    (hn : chainLength L v ≤ n) : gramSchmidtNormed ℂ (powerSequence L v) n = 0 := by
  by_contra h
  have hl := active_index_lt_length L v ⟨n,h⟩
  exact (Nat.not_lt_of_ge hn) hl

theorem right_mixed_energy_length :
    chainLength (PerturbedDynamics.liouvillian (hamiltonian States.energyR))
      (normalizedSeed RightMixed.seed) = 3 := by
  rw [normalized_cyclic_dimension _ _
    (by simpa [RightMixed.chain_zero] using RightMixed.chain_nonzero 0),diagonal_commutator]
  exact RightMixed.cyclic_dimension

theorem right_purified_energy_length :
    chainLength (PerturbedDynamics.liouvillian (hamiltonian PurifiedChain.energies))
      (normalizedSeed PurifiedChain.seed) = 5 := by
  rw [normalized_cyclic_dimension _ _
    (by intro hz; have h := PurifiedChain.seed_norm; simp [hz,hsInner] at h),
    diagonal_commutator]
  exact PurifiedChain.cyclic_dimension

/-- The original mixed witness has exactly three nonzero actual GS vectors. -/
theorem right_mixed_card :
    Fintype.card (GSIndex (powerSequence
      (PerturbedDynamics.liouvillian (States.hR.map Complex.ofReal))
      (normalizedSeed (States.rhoR.map Complex.ofReal)))) = 3 := by
  change chainLength _ _ = 3
  rw [← length_changeBasis rightBasis _ _ rightBasis_unitary rightBasis_unitary_reverse,
    right_hamiltonian_coordinates,right_density_coordinates]
  exact right_mixed_energy_length

theorem right_purified_matrix_card :
    Fintype.card (GSIndex (powerSequence
      (PerturbedDynamics.liouvillian PurifiedCovariance.originalGenerator)
      (normalizedSeed PurifiedCovariance.originalSeed))) = 5 := by
  change chainLength _ _ = 5
  rw [← length_changeBasis PurifiedCovariance.basis _ _
    PurifiedCovariance.basis_unitary PurifiedCovariance.basis_unitary_reverse,
    PurifiedCovariance.generator_coordinates,PurifiedCovariance.seed_coordinates]
  exact right_purified_energy_length

lemma canonical_operator_sequence :
    operatorSequence
      (PurificationBranches.generatorI (States.hR.map Complex.ofReal))
      (PurificationBranches.seed complex_rhoR_posDef.posSemidef) =
    powerSequence (PerturbedDynamics.liouvillian PurifiedCovariance.originalGenerator)
      (normalizedSeed PurifiedCovariance.originalSeed) := by
  have hu := PureShortTime.pureVector_unit
    (PurificationBranches.seed complex_rhoR_posDef.posSemidef)
    (PurificationBranches.seed_unit _ (complex_trace_one _ States.rhoR_trace))
  have he : FactorTwo.pureSeed (PurificationBranches.seed complex_rhoR_posDef.posSemidef) =
      PurifiedCovariance.originalSeed := by
    change Purification.pureSeed complex_rhoR_posDef.posSemidef.sqrt = _
    rw [← complex_rootR_canonical]
    rfl
  rw [he] at hu
  rw [PurificationBranches.generatorI_eq_kronecker]
  funext n
  simp only [operatorSequence,he,powerSequence,normalizedSeed,hu,inv_one,
    Complex.ofReal_one,one_smul,liouvillian_power_rowVectorize]
  rfl

/-- Literal source I-branch operator chain, with its canonical positive root. -/
theorem right_purified_card :
    Fintype.card (GSIndex (operatorSequence
      (PurificationBranches.generatorI (States.hR.map Complex.ofReal))
      (PurificationBranches.seed complex_rhoR_posDef.posSemidef))) = 5 := by
  rw [canonical_operator_sequence]
  exact right_purified_matrix_card

theorem right_mixed_later_zero (n : ℕ) (hn : 3 ≤ n) :
    gramSchmidtNormed ℂ (powerSequence
      (PerturbedDynamics.liouvillian (States.hR.map Complex.ofReal))
      (normalizedSeed (States.rhoR.map Complex.ofReal))) n = 0 := by
  apply later_zero
  simpa only [chainLength,right_mixed_card] using hn

theorem right_purified_later_zero (n : ℕ) (hn : 5 ≤ n) :
    gramSchmidtNormed ℂ (operatorSequence
      (PurificationBranches.generatorI (States.hR.map Complex.ofReal))
      (PurificationBranches.seed complex_rhoR_posDef.posSemidef)) n = 0 := by
  rw [canonical_operator_sequence]
  apply later_zero
  simpa only [chainLength,right_purified_matrix_card] using hn

end
end Krylov.WitnessChainLengths
