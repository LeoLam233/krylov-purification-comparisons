import Krylov.FactorTwoSharpness
import Krylov.FactorTwoTheorem
import Krylov.KrylovTermination

/-! The exact saturating example uses the same normalized Gram–Schmidt
complexity as the universal physical factor-two theorem. -/
namespace Krylov.FactorTwoSharpnessGS
open Matrix
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
open FactorTwoSharpness FactorTwoFinite

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma normed_of_positive_multiple (f : ℕ → E) (n : ℕ) (v : E) (c : ℝ)
    (hc : 0 < c) (hv : ‖v‖ = 1) (h : gramSchmidt ℂ f n = (c : ℂ) • v) :
    gramSchmidtNormed ℂ f n = v := by
  rw [gramSchmidtNormed, h, norm_smul, hv, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hc]
  exact inv_smul_smul₀ (show (c : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hc) v

lemma termination_of_recurrence (L : E →ₗ[ℂ] E) (f : ℕ → E)
    (hf : ∀ n, f (n+1) = L (f n)) {n k : ℕ}
    (hz : gramSchmidtNormed ℂ f n = 0) (hnk : n ≤ k) :
    gramSchmidtNormed ℂ f k = 0 := by
  let C : E →L[ℂ] E := LinearMap.toContinuousLinearMap L
  have he : f = KrylovTermination.sequence C (f 0) := by
    funext j
    induction j with
    | zero => simp [KrylovTermination.sequence]
    | succ j ih => rw [hf, KrylovTermination.sequence_succ, ih]; rfl
  rw [he] at hz ⊢
  exact KrylovTermination.zero_forces_later_zero C (f 0) hz hnk

/-- A terminated orthonormal Gram–Schmidt chain may be summed over its
ordinary finite degree index without changing the general complexity. -/
lemma complexity_eq_finite {d : ℕ} (f : ℕ → E) (v : Fin d → E)
    (hv : Orthonormal ℂ v)
    (hfirst : ∀ i : Fin d, gramSchmidtNormed ℂ f i.val = v i)
    (hlater : ∀ k, d ≤ k → gramSchmidtNormed ℂ f k = 0) (x : E) :
    complexity f x = ∑ i : Fin d, (i.val : ℝ) * ‖⟪v i, x⟫_ℂ‖^2 := by
  classical
  let e : GSIndex f ≃ Fin d :=
    { toFun := fun k => ⟨k.val, by
        by_contra hn
        exact k.property (hlater k.val (Nat.le_of_not_gt hn))⟩
      invFun := fun i => ⟨i.val, by
        change gramSchmidtNormed ℂ f i.val ≠ 0
        rw [hfirst i]
        exact hv.ne_zero i⟩
      left_inv := fun k => by apply Subtype.ext; rfl
      right_inv := fun i => by apply Fin.ext; rfl }
  unfold complexity
  apply Fintype.sum_equiv e
  intro k
  change (k.val : ℝ) * ‖⟪gramSchmidtNormed ℂ f k.val, x⟫_ℂ‖^2 = _
  have h := hfirst (e k)
  change gramSchmidtNormed ℂ f k.val = v (e k) at h
  rw [h]
  rfl

end General

abbrev seed : Fin 3 → ℂ := ![1,0,0]
abbrev stateSeq := stateSequence H seed
abbrev operatorSeq := operatorSequence H seed

def stateBasis (i : Fin 2) : EuclideanSpace ℂ (Fin 3) :=
  UnitaryEvolution.hilbertVector (![seed, ![0,1,0]] i)

def operatorBasis (i : Fin 3) : EuclideanSpace ℂ (Fin 3 × Fin 3) :=
  FactorTwo.rowVectorize (opBasis i)

theorem stateBasis_orthonormal : Orthonormal ℂ stateBasis := by
  apply orthonormal_iff_ite.mpr
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [stateBasis, UnitaryEvolution.hilbertVector, PiLp.inner_apply,
      Fin.sum_univ_succ, RCLike.inner_apply]

theorem operatorBasis_orthonormal : Orthonormal ℂ operatorBasis :=
  opBasis_orthonormal

lemma stateSeq_zero : stateSeq 0 = stateBasis 0 := by
  simp [stateSequence, FactorTwo.hilbertSequence, FactorTwo.statePowerSequence,
    stateBasis, UnitaryEvolution.hilbertVector]

lemma stateSeq_one : stateSeq 1 = stateBasis 1 := by
  apply (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)).injective
  ext i
  fin_cases i <;> simp [stateSequence, FactorTwo.hilbertSequence, FactorTwo.statePowerSequence,
    stateBasis, UnitaryEvolution.hilbertVector, H_eq, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

lemma stateSeq_two : stateSeq 2 = stateSeq 0 := by
  apply (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)).injective
  ext i
  fin_cases i <;>
    norm_num [stateSequence, FactorTwo.hilbertSequence, FactorTwo.statePowerSequence,
      H_eq, pow_two, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma seed_density : FactorTwo.pureSeed seed = opBasis 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [FactorTwo.pureSeed, FactorTwo.outer, opBasis]

lemma operatorSeq_zero : operatorSeq 0 = operatorBasis 0 := by
  simp [operatorSequence, operatorBasis, seed_density]

lemma operatorSeq_one : operatorSeq 1 = ((2*q : ℝ) : ℂ) • operatorBasis 1 := by
  simp only [operatorSequence, pow_one, seed_density, operator_lanczos.1, map_smul]
  rfl

lemma operatorSeq_two : operatorSeq 2 = (2 : ℂ) • operatorBasis 0 +
    (2 : ℂ) • operatorBasis 2 := by
  have hq : ((2*q : ℝ) : ℂ) * ((2*q : ℝ) : ℂ) = 2 := by
    have h : (q : ℂ)^2 = 1/2 := by
      rw [← Complex.ofReal_pow, q_sq]
      norm_num
    push_cast
    linear_combination 4*h
  simp only [operatorSequence, pow_two, Module.End.mul_apply, seed_density,
    operator_lanczos.1, map_smul, operator_lanczos.2.1, smul_add, smul_smul, hq,
    map_add]
  rfl

lemma operatorSeq_three : operatorSeq 3 = (4 : ℂ) • operatorSeq 1 := by
  have hq : ((2*q : ℝ) : ℂ) * ((2*q : ℝ) : ℂ) = 2 := by
    have h : (q : ℂ)^2 = 1/2 := by
      rw [← Complex.ofReal_pow, q_sq]
      norm_num
    push_cast
    linear_combination 4*h
  change FactorTwo.rowVectorize ((FactorTwo.commutator H ^ (2+1))
    (FactorTwo.pureSeed seed)) = _
  rw [pow_succ', Module.End.mul_apply]
  simp only [pow_two, Module.End.mul_apply, seed_density, operator_lanczos.1,
    map_smul, operator_lanczos.2.1, smul_add, smul_smul, hq, map_add,
    operator_lanczos.2.2, operatorSeq_one, operatorBasis]
  module


lemma state_gram_zero : gramSchmidt ℂ stateSeq 0 = stateBasis 0 := by
  exact (gramSchmidt_zero ℂ stateSeq).trans stateSeq_zero

lemma state_gram_one : gramSchmidt ℂ stateSeq 1 = stateBasis 1 := by
  have h01 : ⟪stateBasis 0,stateBasis 1⟫_ℂ = 0 :=
    stateBasis_orthonormal.inner_eq_zero (by decide)
  rw [gramSchmidt_def]
  simp only [Nat.Iio_eq_range, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, state_gram_zero, stateSeq_one, Submodule.orthogonalProjection_singleton,
    h01, zero_div, zero_smul, sub_zero]

lemma state_normed_zero : gramSchmidtNormed ℂ stateSeq 0 = stateBasis 0 := by
  simp [gramSchmidtNormed, state_gram_zero, stateBasis_orthonormal.norm_eq_one]

lemma state_normed_one : gramSchmidtNormed ℂ stateSeq 1 = stateBasis 1 := by
  simp [gramSchmidtNormed, state_gram_one, stateBasis_orthonormal.norm_eq_one]

lemma state_normed_two : gramSchmidtNormed ℂ stateSeq 2 = 0 := by
  apply (KrylovTermination.normed_zero_iff _ _).2
  apply (KrylovTermination.gram_zero_iff_mem _ _).2
  rw [stateSeq_two]
  exact Submodule.subset_span ⟨0, by norm_num, rfl⟩

lemma operator_gram_zero : gramSchmidt ℂ operatorSeq 0 = operatorBasis 0 := by
  exact (gramSchmidt_zero ℂ operatorSeq).trans operatorSeq_zero

lemma operator_gram_one : gramSchmidt ℂ operatorSeq 1 =
    ((2*q : ℝ) : ℂ) • operatorBasis 1 := by
  have h01 : ⟪operatorBasis 0,operatorBasis 1⟫_ℂ = 0 :=
    operatorBasis_orthonormal.inner_eq_zero (by decide)
  rw [gramSchmidt_def]
  simp only [Nat.Iio_eq_range, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, operator_gram_zero, operatorSeq_one,
    Submodule.orthogonalProjection_singleton, inner_smul_right, h01,
    mul_zero, zero_div, zero_smul, sub_zero]

lemma operator_gram_two : gramSchmidt ℂ operatorSeq 2 = (2 : ℂ) • operatorBasis 2 := by
  have h00 : ⟪operatorBasis 0,operatorBasis 0⟫_ℂ = 1 :=
    (orthonormal_iff_ite.mp operatorBasis_orthonormal 0 0).trans (by simp)
  have h02 : ⟪operatorBasis 0,operatorBasis 2⟫_ℂ = 0 :=
    operatorBasis_orthonormal.inner_eq_zero (by decide)
  have h10 : ⟪operatorBasis 1,operatorBasis 0⟫_ℂ = 0 :=
    operatorBasis_orthonormal.inner_eq_zero (by decide)
  have h12 : ⟪operatorBasis 1,operatorBasis 2⟫_ℂ = 0 :=
    operatorBasis_orthonormal.inner_eq_zero (by decide)
  rw [gramSchmidt_def]
  simp only [Nat.Iio_eq_range, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, operator_gram_zero, operator_gram_one, operatorSeq_two,
    Submodule.orthogonalProjection_singleton, inner_smul_right, inner_smul_left,
    inner_add_right, h00, h02, h10, h12, operatorBasis_orthonormal.norm_eq_one,
    mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, zero_div,
    zero_smul, one_pow, Complex.ofReal_one, div_one]
  module

lemma operator_normed_zero : gramSchmidtNormed ℂ operatorSeq 0 = operatorBasis 0 := by
  simp [gramSchmidtNormed, operator_gram_zero, operatorBasis_orthonormal.norm_eq_one]

lemma operator_normed_one : gramSchmidtNormed ℂ operatorSeq 1 = operatorBasis 1 :=
  normed_of_positive_multiple _ _ _ (2*q) lanczos_coupling_positive
    (operatorBasis_orthonormal.norm_eq_one 1) operator_gram_one

lemma operator_normed_two : gramSchmidtNormed ℂ operatorSeq 2 = operatorBasis 2 :=
  normed_of_positive_multiple _ _ _ 2 (by norm_num)
    (operatorBasis_orthonormal.norm_eq_one 2) (by simpa using operator_gram_two)

lemma operator_normed_three : gramSchmidtNormed ℂ operatorSeq 3 = 0 := by
  apply (KrylovTermination.normed_zero_iff _ _).2
  apply (KrylovTermination.gram_zero_iff_mem _ _).2
  rw [operatorSeq_three]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by norm_num, rfl⟩)

lemma state_normed_later (k : ℕ) (hk : 2 ≤ k) : gramSchmidtNormed ℂ stateSeq k = 0 := by
  let e := WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)
  let L := e.symm.toLinearMap.comp (H.mulVecLin.comp e.toLinearMap)
  apply termination_of_recurrence L stateSeq _ state_normed_two hk
  intro n
  change e.symm (H ^ (n+1) *ᵥ seed) = e.symm (H *ᵥ (H ^ n *ᵥ seed))
  rw [pow_succ', Matrix.mulVec_mulVec]

lemma operator_normed_later (k : ℕ) (hk : 3 ≤ k) :
    gramSchmidtNormed ℂ operatorSeq k = 0 := by
  let e := (FactorTwo.rowVectorize : Mat ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 3 × Fin 3))
  let L := e.toLinearMap.comp ((FactorTwo.commutator H).comp e.symm.toLinearMap)
  apply termination_of_recurrence L operatorSeq _ operator_normed_three hk
  intro n
  change e ((FactorTwo.commutator H ^ (n+1)) (FactorTwo.pureSeed seed)) =
    e (FactorTwo.commutator H ((FactorTwo.commutator H ^ n) (FactorTwo.pureSeed seed)))
  rw [pow_succ', Module.End.mul_apply]


/-- Identification with the actual matrix-exponential evolved vector. -/
lemma evolvedVector_eq (t : ℝ) : UnitaryEvolution.evolvedVector H seed t =
    UnitaryEvolution.hilbertVector (ψ t) := by
  apply (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)).injective
  ext i
  simp [UnitaryEvolution.evolvedVector, UnitaryEvolution.hilbertVector,
    UnitaryEvolution.propagator, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, ψ]

lemma evolvedDensity_eq (t : ℝ) :
    FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector H seed t)
      (UnitaryEvolution.evolvedVector H seed t) = FactorTwo.rowVectorize (σ t) := by
  rw [evolvedVector_eq]
  rfl

/-- The explicit state complexity is exactly the universal theorem's
normalized Gram–Schmidt state complexity, at every real time. -/
theorem state_complexity_eq (t : ℝ) :
    complexity stateSeq (UnitaryEvolution.evolvedVector H seed t) = stateComplexity t := by
  rw [complexity_eq_finite stateSeq stateBasis stateBasis_orthonormal
    (by intro i; fin_cases i; exact state_normed_zero; exact state_normed_one)
    state_normed_later, evolvedVector_eq, state_evolution, state_complexity]
  simp [Fin.sum_univ_succ, stateBasis, UnitaryEvolution.hilbertVector,
    PiLp.inner_apply, RCLike.inner_apply, norm_mul, Complex.norm_I,
    ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The explicit operator complexity is exactly the universal theorem's
normalized Gram–Schmidt commutator complexity, at every real time. -/
theorem operator_complexity_eq (t : ℝ) :
    complexity operatorSeq
      (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector H seed t)
        (UnitaryEvolution.evolvedVector H seed t)) = operatorComplexity t := by
  rw [complexity_eq_finite operatorSeq operatorBasis operatorBasis_orthonormal
    (by intro i; fin_cases i; exact operator_normed_zero; exact operator_normed_one;
        exact operator_normed_two)
    operator_normed_later, evolvedDensity_eq]
  rfl

/-- This physical example saturates factor two in precisely the same API as
`FactorTwoTheorem.finite_dimensional_factor_two`. -/
theorem exact_saturation (t : ℝ) :
    complexity (operatorSequence H seed)
      (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector H seed t)
        (UnitaryEvolution.evolvedVector H seed t)) =
      2 * complexity (stateSequence H seed) (UnitaryEvolution.evolvedVector H seed t) := by
  rw [operator_complexity_eq, state_complexity_eq, FactorTwoSharpness.exact_saturation]

/-- The seed satisfies the physical theorem's actual Euclidean unit-norm
hypothesis. -/
theorem seed_unit : ‖UnitaryEvolution.hilbertVector seed‖ = 1 :=
  stateBasis_orthonormal.norm_eq_one 0

/-- Every coefficient larger than two fails for these same generic Krylov
complexities, for a normalized seed and Hermitian Hamiltonian. -/
theorem excludes_larger_multiplier {c : ℝ} (hc : 2 < c) :
    complexity (operatorSequence H seed)
      (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector H seed (Real.pi/2))
        (UnitaryEvolution.evolvedVector H seed (Real.pi/2))) <
      c * complexity (stateSequence H seed)
        (UnitaryEvolution.evolvedVector H seed (Real.pi/2)) := by
  rw [operator_complexity_eq, state_complexity_eq]
  exact FactorTwoSharpness.excludes_larger_multiplier hc


/-- Any multiplier valid for all normalized physical seeds and Hermitian
three-dimensional Hamiltonians is at most two. -/
theorem universal_multiplier_le_two (c : ℝ)
    (hc : ∀ (G : Mat) (v : Fin 3 → ℂ) (t : ℝ), G.IsHermitian →
      ‖UnitaryEvolution.hilbertVector v‖ = 1 →
      c * complexity (stateSequence G v) (UnitaryEvolution.evolvedVector G v t) ≤
        complexity (operatorSequence G v)
          (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector G v t)
            (UnitaryEvolution.evolvedVector G v t))) : c ≤ 2 := by
  by_contra h
  exact (not_le_of_gt (excludes_larger_multiplier (lt_of_not_ge h)))
    (hc H seed (Real.pi/2) H_hermitian seed_unit)

end
end Krylov.FactorTwoSharpnessGS
