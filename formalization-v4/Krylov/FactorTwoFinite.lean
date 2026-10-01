import Krylov.FactorTwo

/-! Finite nonzero Gram-Schmidt coordinates and their genuine flag projections. -/
namespace Krylov.FactorTwoFinite
open Matrix
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Actual nonzero normalized Gram-Schmidt indices, retaining their original
degree. This type is finite without assuming a nonterminating chain. -/
def GSIndex (f : ℕ → E) := {k : ℕ | gramSchmidtNormed ℂ f k ≠ 0}

instance gsIndexFinite (f : ℕ → E) : Finite (GSIndex f) :=
  (gramSchmidt_orthonormal' f).linearIndependent.finite

noncomputable instance gsIndexFintype (f : ℕ → E) : Fintype (GSIndex f) := Fintype.ofFinite _

def gsFamily (f : ℕ → E) : GSIndex f → E := fun k => gramSchmidtNormed ℂ f k.val

theorem gsFamily_orthonormal (f : ℕ → E) : Orthonormal ℂ (gsFamily f) :=
  gramSchmidt_orthonormal' f

def prefixIndices (f : ℕ → E) (n : ℕ) : Finset (GSIndex f) := by
  classical
  exact Finset.univ.filter (fun k => k.val ≤ n)

def prefixSpan (f : ℕ → E) (n : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ (f '' Set.Iic n)

def cyclicSpan (f : ℕ → E) : Submodule ℂ E := Submodule.span ℂ (Set.range f)

/-- Removing zero Gram-Schmidt vectors preserves every exact prefix span. -/
theorem prefixSpan_eq (f : ℕ → E) (n : ℕ) :
    prefixSpan f n = FactorTwo.finiteOrthoSpan (gsFamily f) (prefixIndices f n) := by
  classical
  unfold prefixSpan
  rw [← span_gramSchmidt_Iic ℂ f n, ← span_gramSchmidtNormed f (Set.Iic n)]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨k, hkn, rfl⟩
    by_cases hk : gramSchmidtNormed ℂ f k = 0
    · rw [hk]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨k, hk⟩, by simpa [prefixIndices] using hkn, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨k, hk, rfl⟩
    exact Submodule.subset_span ⟨k.val, by simpa [prefixIndices] using hk, rfl⟩

/-- Removing zero vectors also preserves the full cyclic span. -/
theorem cyclicSpan_eq (f : ℕ → E) :
    cyclicSpan f = FactorTwo.finiteOrthoSpan (gsFamily f) Finset.univ := by
  classical
  unfold cyclicSpan
  rw [← span_gramSchmidt ℂ f, ← span_gramSchmidtNormed_range f]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨k, rfl⟩
    by_cases hk : gramSchmidtNormed ℂ f k = 0
    · rw [hk]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨k, hk⟩, by simp, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨k, hk, rfl⟩
    exact Submodule.subset_span ⟨k.val, rfl⟩

def probability (f : ℕ → E) (x : E) (k : GSIndex f) : ℝ := ‖⟪gsFamily f k, x⟫_ℂ‖ ^ 2

def complexity (f : ℕ → E) (x : E) : ℝ :=
  ∑ k : GSIndex f, (k.val : ℝ) * probability f x k

/-- Exact coordinate formula for the actual polynomial-prefix projection. -/
theorem prefix_projection_mass (f : ℕ → E) (n : ℕ) (x : E) :
    ‖(prefixSpan f n).orthogonalProjection x‖ ^ 2 =
      ∑ k ∈ prefixIndices f n, probability f x k := by
  rw [prefixSpan_eq]
  exact FactorTwo.orthonormal_projection_mass (gsFamily f) (gsFamily_orthonormal f) _ x

/-- Parseval normalization on the actual cyclic subspace. -/
theorem total_probability (f : ℕ → E) (x : E) (hx : x ∈ cyclicSpan f) :
    (∑ k : GSIndex f, probability f x k) = ‖x‖ ^ 2 := by
  have h := FactorTwo.orthonormal_projection_mass (gsFamily f) (gsFamily_orthonormal f)
    Finset.univ x
  rw [← cyclicSpan_eq f] at h
  have he := (Submodule.orthogonalProjection_eq_self_iff).mpr hx
  change ‖((cyclicSpan f).orthogonalProjection x : E)‖ ^ 2 = _ at h
  rw [he] at h
  simpa [probability] using h.symm

/-- Finite normalization turns a degree-tail sum into one minus a prefix mass. -/
theorem tail_complement {κ : Type*} [Fintype κ] (index : κ → ℕ) (p : κ → ℝ)
    (hp : ∑ k, p k = 1) (n : ℕ) :
    (∑ k, if n < index k then p k else 0) =
      1 - ∑ k ∈ Finset.univ.filter (fun k => index k ≤ n), p k := by
  classical
  have hsplit : (∑ k, if n < index k then p k else 0) +
      (∑ k ∈ Finset.univ.filter (fun k => index k ≤ n), p k) = ∑ k, p k := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : n < index k
    · simp [hk, Nat.not_le.mpr hk]
    · simp [hk, Nat.le_of_not_gt hk]
  linarith

end General
section Physical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stateSequence (G : FactorTwo.Operator ι) (ψ : ι → ℂ) : ℕ → EuclideanSpace ℂ ι :=
  FactorTwo.hilbertSequence (FactorTwo.statePowerSequence G ψ)

def operatorSequence (G : FactorTwo.Operator ι) (ψ : ι → ℂ) :
    ℕ → EuclideanSpace ℂ (ι × ι) :=
  fun k => FactorTwo.rowVectorize ((FactorTwo.commutator G ^ k) (FactorTwo.pureSeed ψ))

def tensorIndices (f : ℕ → EuclideanSpace ℂ ι) (n : ℕ) :
    Finset (GSIndex f × GSIndex f) := by
  classical
  exact Finset.univ.filter (fun p => p.1.val + p.2.val ≤ n)

def gsTensorFlag (f : ℕ → EuclideanSpace ℂ ι) (n : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (ι × ι)) :=
  (FactorTwo.sequenceTensorFlag
    (fun k => WithLp.linearEquiv 2 ℂ (ι → ℂ) (gramSchmidtNormed ℂ f k)) n).map FactorTwo.rowVectorize.toLinearMap

/-- The actual Gram-Schmidt product flag equals the finite nonzero product
coordinate span; zero terms disappear without changing the subspace. -/
theorem gsTensorFlag_eq (f : ℕ → EuclideanSpace ℂ ι) (n : ℕ) :
    gsTensorFlag f n = FactorTwo.finiteOrthoSpan
      (fun p : GSIndex f × GSIndex f => FactorTwo.hilbertOuter (gsFamily f p.1) (gsFamily f p.2))
      (tensorIndices f n) := by
  classical
  unfold gsTensorFlag FactorTwo.sequenceTensorFlag
  rw [Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨A, ⟨i, j, hij, rfl⟩, rfl⟩
    by_cases hi : gramSchmidtNormed ℂ f i = 0
    · simp [hi]
    by_cases hj : gramSchmidtNormed ℂ f j = 0
    · simp [hj]
    exact Submodule.subset_span ⟨(⟨i, hi⟩, ⟨j, hj⟩), by simpa [tensorIndices] using hij, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨p, hp, rfl⟩
    refine Submodule.subset_span ⟨_, ⟨p.1.val, p.2.val, ?_, rfl⟩, rfl⟩
    simpa [tensorIndices] using hp

theorem actual_tensor_flag_eq (G : FactorTwo.Operator ι) (ψ : ι → ℂ) (n : ℕ) :
    FactorTwo.hilbertTensorFlag G ψ n = gsTensorFlag (stateSequence G ψ) n := rfl

/-- Product projection mass for the actual physical state Krylov flag. -/
theorem actual_tensor_projection_mass (G : FactorTwo.Operator ι) (ψ : ι → ℂ)
    (n : ℕ) (x : EuclideanSpace ℂ ι) :
    ‖(FactorTwo.hilbertTensorFlag G ψ n).orthogonalProjection (FactorTwo.hilbertOuter x x)‖ ^ 2 =
      ∑ p ∈ tensorIndices (stateSequence G ψ) n,
        probability (stateSequence G ψ) x p.1 * probability (stateSequence G ψ) x p.2 := by
  classical
  rw [actual_tensor_flag_eq, gsTensorFlag_eq]
  exact FactorTwo.tensor_projection_mass _ (gsFamily_orthonormal _) _ x

/-- The matrix commutator flag transported to Hilbert--Schmidt coordinates is
exactly the prefix span of its actual commutator-power sequence. -/
theorem actual_operator_flag_eq (G : FactorTwo.Operator ι) (ψ : ι → ℂ) (n : ℕ) :
    FactorTwo.hilbertOperatorFlag G ψ n = prefixSpan (operatorSequence G ψ) n := by
  unfold FactorTwo.hilbertOperatorFlag FactorTwo.operatorKrylovFlag prefixSpan
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨A, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩

theorem actual_operator_projection_mass (G : FactorTwo.Operator ι) (ψ : ι → ℂ)
    (n : ℕ) (x : EuclideanSpace ℂ (ι × ι)) :
    ‖(FactorTwo.hilbertOperatorFlag G ψ n).orthogonalProjection x‖ ^ 2 =
      ∑ k ∈ prefixIndices (operatorSequence G ψ) n, probability (operatorSequence G ψ) x k := by
  rw [actual_operator_flag_eq]
  exact prefix_projection_mass _ _ _

theorem pure_norm_square_of_unit (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) :
    ‖FactorTwo.hilbertOuter x x‖ ^ 2 = 1 := by
  rw [@norm_sq_eq_re_inner ℂ, FactorTwo.hilbertOuter_inner, inner_self_eq_norm_sq_to_K, hx]
  norm_num

/-- Probability-tail domination for the actual state and operator
Gram-Schmidt chains. All flag/projection identifications are derived above.
Only unit norm and membership of the final state in the two actual cyclic
spaces are required; Hamiltonian evolution will supply those memberships. -/
theorem actual_tail_domination (G : FactorTwo.Operator ι) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (x : EuclideanSpace ℂ ι) (hunit : ‖x‖ = 1)
    (hx : x ∈ cyclicSpan (stateSequence G ψ))
    (hχ : FactorTwo.hilbertOuter x x ∈ cyclicSpan (operatorSequence G ψ)) (n : ℕ) :
    (∑ i : GSIndex (stateSequence G ψ), ∑ j : GSIndex (stateSequence G ψ),
      if n < i.val + j.val then probability (stateSequence G ψ) x i *
        probability (stateSequence G ψ) x j else 0) ≤
    ∑ k : GSIndex (operatorSequence G ψ), if n < k.val then
      probability (operatorSequence G ψ) (FactorTwo.hilbertOuter x x) k else 0 := by
  classical
  have hp : (∑ k : GSIndex (stateSequence G ψ), probability (stateSequence G ψ) x k) = 1 := by
    rw [total_probability _ _ hx, hunit]; norm_num
  have hq : (∑ k : GSIndex (operatorSequence G ψ),
      probability (operatorSequence G ψ) (FactorTwo.hilbertOuter x x) k) = 1 := by
    rw [total_probability _ _ hχ, pure_norm_square_of_unit x hunit]
  have hprod : (∑ p : GSIndex (stateSequence G ψ) × GSIndex (stateSequence G ψ),
      probability (stateSequence G ψ) x p.1 * probability (stateSequence G ψ) x p.2) = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hp, mul_one]
    exact hp
  have hgeom := FactorTwo.physical_projection_tail G hG ψ
    (WithLp.linearEquiv 2 ℂ (ι → ℂ) x) n
  change 1 - ‖(FactorTwo.hilbertTensorFlag G ψ n).orthogonalProjection
      (FactorTwo.hilbertOuter x x)‖ ^ 2 ≤
    1 - ‖(FactorTwo.hilbertOperatorFlag G ψ n).orthogonalProjection
      (FactorTwo.hilbertOuter x x)‖ ^ 2 at hgeom
  rw [actual_tensor_projection_mass, actual_operator_projection_mass] at hgeom
  have ht := tail_complement (fun p : GSIndex (stateSequence G ψ) × GSIndex (stateSequence G ψ) =>
    p.1.val + p.2.val) (fun p => probability (stateSequence G ψ) x p.1 *
      probability (stateSequence G ψ) x p.2) hprod n
  have ho := tail_complement (fun k : GSIndex (operatorSequence G ψ) => k.val)
    (probability (operatorSequence G ψ) (FactorTwo.hilbertOuter x x)) hq n
  change _ = 1 - ∑ p ∈ tensorIndices (stateSequence G ψ) n,
    probability (stateSequence G ψ) x p.1 * probability (stateSequence G ψ) x p.2 at ht
  change _ = 1 - ∑ k ∈ prefixIndices (operatorSequence G ψ) n,
    probability (operatorSequence G ψ) (FactorTwo.hilbertOuter x x) k at ho
  rw [← ht, ← ho] at hgeom
  simpa only [Fintype.sum_prod_type] using hgeom

/-- Finite geometric factor-two theorem for the actual normalized
Gram-Schmidt state and pure-density operator chains. -/
theorem factor_two (G : FactorTwo.Operator ι) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (x : EuclideanSpace ℂ ι) (hunit : ‖x‖ = 1)
    (hx : x ∈ cyclicSpan (stateSequence G ψ))
    (hχ : FactorTwo.hilbertOuter x x ∈ cyclicSpan (operatorSequence G ψ)) :
    2 * complexity (stateSequence G ψ) x ≤
      complexity (operatorSequence G ψ) (FactorTwo.hilbertOuter x x) := by
  classical
  let S := Finset.univ.sup (fun k : GSIndex (stateSequence G ψ) => k.val)
  let O := Finset.univ.sup (fun k : GSIndex (operatorSequence G ψ) => k.val)
  let N := max (S + S) O
  have hi : ∀ i ∈ (Finset.univ : Finset (GSIndex (stateSequence G ψ))),
      ∀ j ∈ (Finset.univ : Finset (GSIndex (stateSequence G ψ))), i.val + j.val ≤ N := by
    intro i hi j hj
    exact le_trans (Nat.add_le_add (Finset.le_sup hi) (Finset.le_sup hj)) (le_max_left _ _)
  have hj : ∀ k ∈ (Finset.univ : Finset (GSIndex (operatorSequence G ψ))), k.val ≤ N := by
    intro k hk
    exact le_trans (Finset.le_sup hk) (le_max_right _ _)
  have hp : (∑ k : GSIndex (stateSequence G ψ), probability (stateSequence G ψ) x k) = 1 := by
    rw [total_probability _ _ hx, hunit]; norm_num
  have h := Krylov.factor_two_of_tail_domination Finset.univ Finset.univ
    (fun k : GSIndex (stateSequence G ψ) => k.val)
    (fun k : GSIndex (operatorSequence G ψ) => k.val)
    (probability (stateSequence G ψ) x)
    (probability (operatorSequence G ψ) (FactorTwo.hilbertOuter x x)) N
    (by simpa using hp) hi hj (by
      intro n hn
      simpa using actual_tail_domination G hG ψ x hunit hx hχ n)
  simpa only [complexity] using h

end Physical

end
end Krylov.FactorTwoFinite
