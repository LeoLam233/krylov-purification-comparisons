import Krylov.PerturbedDynamics

/-! Return bounds for actual normalized Gram–Schmidt chains, with their true
cyclic lengths. Normalization and the zeroth return amplitude are derived. -/
namespace Krylov.ActualReturnBounds
open FactorTwoFinite PerturbedDynamics TaylorRemainder
open scoped InnerProductSpace BigOperators
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Number of nonzero vectors in the actual normalized Krylov chain. -/
def chainLength (L : E →L[ℂ] E) (v : E) : ℕ := Fintype.card (GSIndex (powerSequence L v))

/-- Every retained original degree is smaller than the true chain length. -/
theorem active_index_lt_length (L : E →L[ℂ] E) (v : E)
    (k : GSIndex (powerSequence L v)) : k.val < chainLength L v := by
  let e : Fin (k.val+1) → GSIndex (powerSequence L v) := fun i =>
    ⟨i.val,KrylovTermination.nonzero_downward L v k.property (by omega)⟩
  have he : Function.Injective e := by
    intro i j h
    exact Fin.ext (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective e he
  simpa [chainLength] using hc

/-- This length is exactly the cyclic dimension, not the ambient dimension. -/
theorem length_eq_cyclic_finrank (L : E →L[ℂ] E) (v : E) :
    chainLength L v = Module.finrank ℂ (cyclicSpan (powerSequence L v)) := by
  rw [cyclicSpan_eq]
  have he : FactorTwo.finiteOrthoSpan (gsFamily (powerSequence L v)) Finset.univ =
      Submodule.span ℂ (Set.range (gsFamily (powerSequence L v))) := by
    unfold FactorTwo.finiteOrthoSpan
    congr 1
    ext x
    simp
  rw [he]
  change Fintype.card (GSIndex (powerSequence L v)) =
    Module.finrank ℂ (Submodule.span ℂ (Set.range (gsFamily (powerSequence L v))))
  exact (finrank_span_eq_card (gsFamily_orthonormal (powerSequence L v)).linearIndependent).symm

theorem evolution_mem_cyclic (L : E →L[ℂ] E) (v : E) (t : ℝ) :
    evolution (skewGenerator L) v t ∈ cyclicSpan (powerSequence L v) := by
  unfold evolution
  rw [NormedSpace.exp_eq_exp ℝ ℂ]
  have ht : t • skewGenerator L = (-((t:ℂ)*Complex.I)) • L := by
    ext x
    simp only [skewGenerator,ContinuousLinearMap.smul_apply,smul_neg,neg_smul,
      smul_smul,neg_mul,mul_neg,neg_neg]
    rw [← smul_assoc,Complex.real_smul]
  rw [ht]
  exact CyclicEvolution.exp_end_apply_mem_cyclic L v _

/-- Generic source return inequality, for a unit vector in an actual cyclic
space and actual GS probabilities. -/
theorem cyclic_return_bounds (L : E →L[ℂ] E) (v x : E) (hv : ‖v‖=1)
    (hx : x ∈ cyclicSpan (powerSequence L v)) (hxn : ‖x‖=1) :
    1-‖⟪v,x⟫_ℂ‖^2 ≤ complexity (powerSequence L v) x ∧
      complexity (powerSequence L v) x ≤
        ((chainLength L v : ℝ)-1)*(1-‖⟪v,x⟫_ℂ‖^2) := by
  classical
  let f := powerSequence L v
  have hz : gramSchmidtNormed ℂ f 0 = v := by
    have hg : gramSchmidt ℂ f 0 = f 0 := gramSchmidt_zero ℂ f
    rw [gramSchmidtNormed,hg]
    change ((‖v‖:ℂ)⁻¹) • v = v
    simp [hv]
  have hvne : v≠0 := by intro h; simp [h] at hv
  let k0 : GSIndex f := ⟨0,by change gramSchmidtNormed ℂ f 0≠0; rw [hz]; exact hvne⟩
  have hk0 : gsFamily f k0 = v := hz
  have hreturn : probability f x k0 = ‖⟪v,x⟫_ℂ‖^2 := by rw [probability,hk0]
  have hsum : ∑ k : GSIndex f, probability f x k = 1 := by
    rw [total_probability _ _ hx,hxn]
    norm_num
  have hidx (k : GSIndex f) : k.val=0 ↔ k=k0 := by
    constructor
    · intro h; exact Subtype.ext h
    · intro h; subst k; rfl
  have hmass : (∑ k : GSIndex f, if k=k0 then 0 else probability f x k) =
      1-‖⟪v,x⟫_ℂ‖^2 := by
    have hsplit : (∑ k : GSIndex f, if k=k0 then 0 else probability f x k) +
        probability f x k0 = ∑ k : GSIndex f, probability f x k := by
      have he : (∑ k : GSIndex f, if k=k0 then probability f x k else 0) =
          probability f x k0 := by simp
      rw [← he,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    rw [hsum,hreturn] at hsplit
    linarith
  constructor
  · rw [← hmass]
    unfold complexity
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : k=k0
    · subst k; simp [k0]
    · simp only [hk,↓reduceIte]
      have hn : (1:ℝ)≤k.val := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (mt (hidx k).mp hk))
      have hp : 0≤probability f x k := sq_nonneg _
      nlinarith
  · rw [← hmass,Finset.mul_sum]
    unfold complexity
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : k=k0
    · subst k; simp [k0]
    · simp only [hk,↓reduceIte]
      have hn : (k.val:ℝ)≤(chainLength L v:ℝ)-1 := by
        have h := active_index_lt_length L v k
        have h' : k.val+1≤chainLength L v := h
        have hR : (k.val:ℝ)+1≤(chainLength L v:ℝ) := by exact_mod_cast h'
        linarith
      exact mul_le_mul_of_nonneg_right hn (sq_nonneg _)

/-- Actual all-time normalized GS return bound for any finite Hermitian
operator. No probability, completeness or termination premises are supplied. -/
theorem actual_return_bounds (L : E →L[ℂ] E) (hL : IsSelfAdjoint L)
    (v : E) (hv : ‖v‖=1) (t : ℝ) :
    1-‖⟪v,evolution (skewGenerator L) v t⟫_ℂ‖^2 ≤ actualComplexity L v t ∧
      actualComplexity L v t ≤ ((chainLength L v:ℝ)-1)*
        (1-‖⟪v,evolution (skewGenerator L) v t⟫_ℂ‖^2) := by
  exact cyclic_return_bounds L v _ hv (evolution_mem_cyclic L v t)
    (by rw [evolution_norm L hL,hv])
end
end Krylov.ActualReturnBounds
