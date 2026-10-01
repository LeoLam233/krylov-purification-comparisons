import Mathlib

/-!
# Finite-chain bounds and the finite tail-sum mechanism

This file formalizes the probability-theoretic return bound in
`paper/sections/02_framework.tex` and the finite tail-sum step in
`paper/sections/04_factor_two.tex` of revision
`ea43fcc3fc033d7c6ce0887d5747c05868879508`.

The theorem `factor_two_of_tail_domination` is deliberately conditional on
its displayed tail domination hypothesis. The nested orthogonal projection
lemmas below independently establish the geometric monotonicity used in that
hypothesis. This file does not identify physical Krylov flags with these
subspaces, or construct Hamiltonian evolution or the tensor-product flags.
-/

open scoped BigOperators

namespace Krylov

/-- Index-weighted probability of a finite chain with nodes `0, ..., N`. -/
noncomputable def finiteComplexity (N : ℕ) (p : Fin (N + 1) → ℝ) : ℝ :=
  ∑ i, (i.val : ℝ) * p i

/-- The return bound for an arbitrary normalized, nonnegative finite chain.
Here `N` is the maximum index, so the chain length is `N + 1`. -/
theorem finite_return_bounds (N : ℕ) (p : Fin (N + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    1 - p 0 ≤ finiteComplexity N p ∧
      finiteComplexity N p ≤ (N : ℝ) * (1 - p 0) := by
  have hmass : (∑ i : Fin N, p i.succ) = 1 - p 0 := by
    rw [Fin.sum_univ_succ] at hsum
    linarith
  have hc : finiteComplexity N p =
      ∑ i : Fin N, ((i.val : ℝ) + 1) * p i.succ := by
    simp [finiteComplexity, Fin.sum_univ_succ, Nat.cast_add, Nat.cast_one]
  constructor
  · rw [hc, ← hmass]
    apply Finset.sum_le_sum
    intro i _
    have hi : (1 : ℝ) ≤ (i.val : ℝ) + 1 := by
      have hival : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      linarith
    simpa using mul_le_mul_of_nonneg_right hi (hp i.succ)
  · rw [hc, ← hmass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : (i.val : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    exact mul_le_mul_of_nonneg_right hi (hp i.succ)

/-- The same return bound with the return probability supplied by a complex
amplitude. No dynamical claim about that amplitude is assumed. -/
theorem finite_return_amplitude_bounds (N : ℕ) (p : Fin (N + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (A : ℂ) (hreturn : p 0 = ‖A‖ ^ 2) :
    1 - ‖A‖ ^ 2 ≤ finiteComplexity N p ∧
      finiteComplexity N p ≤ (N : ℝ) * (1 - ‖A‖ ^ 2) := by
  simpa [hreturn] using finite_return_bounds N p hp hsum

/-- The `D ≤ C ≤ 8D` corollary for at most five nodes, assuming the
return amplitude is real and belongs to `[0,1]`. The matrix-positivity
argument that supplies those amplitude hypotheses is a separate statement. -/
theorem finite_loss_bounds (N : ℕ) (p : Fin (N + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (A : ℝ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hreturn : p 0 = A ^ 2) (hN : N ≤ 4) :
    1 - A ≤ finiteComplexity N p ∧ finiteComplexity N p ≤ 8 * (1 - A) := by
  obtain ⟨hlo, hhi⟩ := finite_return_bounds N p hp hsum
  rw [hreturn] at hlo hhi
  have hAA : A ^ 2 ≤ A := by
    nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hA1)]
  have hmass : 0 ≤ 1 - A ^ 2 := by nlinarith
  have hNR : (N : ℝ) ≤ 4 := by exact_mod_cast hN
  have hscale := mul_le_mul_of_nonneg_right hNR hmass
  constructor <;> nlinarith

/-- A finite arithmetic tail-counting identity. -/
theorem sum_lt_indicator (N k : ℕ) (hk : k ≤ N) (a : ℝ) :
    (∑ n ∈ Finset.range N, if n < k then a else 0) = (k : ℝ) * a := by
  induction N generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases h : k ≤ N
      · rw [ih k h]
        simp [Nat.not_lt.mpr h]
      · have hk' : k = N + 1 := by omega
        subst k
        have hinner : (∑ n ∈ Finset.range N, if n < N + 1 then a else 0) =
            ∑ _n ∈ Finset.range N, a := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [Finset.mem_range] at hn
          simp [show n < N + 1 by omega]
        rw [hinner]
        simp [Nat.cast_add, Nat.cast_one, add_mul]

/-- Finite tail-sum identity for arbitrary natural-valued indices. -/
theorem finite_tail_sum {α : Type*} (s : Finset α) (index : α → ℕ)
    (p : α → ℝ) (N : ℕ) (hindex : ∀ a ∈ s, index a ≤ N) :
    (∑ n ∈ Finset.range N, ∑ a ∈ s, if n < index a then p a else 0) =
      ∑ a ∈ s, (index a : ℝ) * p a := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  exact sum_lt_indicator N (index a) (hindex a ha) (p a)

/-- First moments are ordered by finite tail domination. Probability
normalization and nonnegativity are not needed for this algebraic step. -/
theorem first_moment_le_of_tail_domination {α β : Type*}
    (s : Finset α) (t : Finset β) (i : α → ℕ) (j : β → ℕ)
    (p : α → ℝ) (q : β → ℝ) (N : ℕ)
    (hi : ∀ a ∈ s, i a ≤ N) (hj : ∀ b ∈ t, j b ≤ N)
    (htail : ∀ n < N,
      (∑ a ∈ s, if n < i a then p a else 0) ≤
        ∑ b ∈ t, if n < j b then q b else 0) :
    (∑ a ∈ s, (i a : ℝ) * p a) ≤ ∑ b ∈ t, (j b : ℝ) * q b := by
  rw [← finite_tail_sum s i p N hi, ← finite_tail_sum t j q N hj]
  exact Finset.sum_le_sum fun n hn => htail n (Finset.mem_range.mp hn)

/-- A normalized product distribution has twice its marginal first moment. -/
theorem product_first_moment {α : Type*} (s : Finset α) (i : α → ℕ)
    (p : α → ℝ) (hsum : ∑ a ∈ s, p a = 1) :
    (∑ a ∈ s, ∑ b ∈ s, ((i a + i b : ℕ) : ℝ) * (p a * p b)) =
      2 * ∑ a ∈ s, (i a : ℝ) * p a := by
  simp_rw [Nat.cast_add, add_mul]
  simp_rw [Finset.sum_add_distrib]
  have hleft : (∑ a ∈ s, ∑ b ∈ s, (i a : ℝ) * (p a * p b)) =
      ∑ a ∈ s, (i a : ℝ) * p a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.mul_sum]
    rw [← Finset.mul_sum, hsum]
    ring
  have hright : (∑ a ∈ s, ∑ b ∈ s, (i b : ℝ) * (p a * p b)) =
      ∑ b ∈ s, (i b : ℝ) * p b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    simp_rw [show ∀ a, (i b : ℝ) * (p a * p b) = ((i b : ℝ) * p b) * p a
      from fun a => by ring]
    rw [← Finset.mul_sum, hsum, mul_one]
  rw [hleft, hright]
  ring

/-- Tail summation for the sum of two independently distributed indices. -/
theorem product_finite_tail_sum {α : Type*} (s : Finset α) (i : α → ℕ)
    (p : α → ℝ) (N : ℕ) (hp : ∑ a ∈ s, p a = 1)
    (hi : ∀ a ∈ s, ∀ b ∈ s, i a + i b ≤ N) :
    (∑ n ∈ Finset.range N,
      ∑ a ∈ s, ∑ b ∈ s, if n < i a + i b then p a * p b else 0) =
      2 * ∑ a ∈ s, (i a : ℝ) * p a := by
  classical
  have h := finite_tail_sum (s ×ˢ s) (fun ab => i ab.1 + i ab.2)
    (fun ab => p ab.1 * p ab.2) N (by
      intro ab hab
      exact hi ab.1 (Finset.mem_product.mp hab).1 ab.2 (Finset.mem_product.mp hab).2)
  simpa only [Finset.sum_product, product_first_moment s i p hp] using h

/-- The finite factor-two implication from the displayed tail domination
hypothesis. This is the tail-sum step, not an unconditional physical theorem. -/
theorem factor_two_of_tail_domination {α β : Type*}
    (s : Finset α) (t : Finset β) (i : α → ℕ) (j : β → ℕ)
    (p : α → ℝ) (q : β → ℝ) (N : ℕ)
    (hp : ∑ a ∈ s, p a = 1)
    (hi : ∀ a ∈ s, ∀ b ∈ s, i a + i b ≤ N)
    (hj : ∀ b ∈ t, j b ≤ N)
    (htail : ∀ n < N,
      (∑ a ∈ s, ∑ b ∈ s, if n < i a + i b then p a * p b else 0) ≤
        ∑ b ∈ t, if n < j b then q b else 0) :
    2 * (∑ a ∈ s, (i a : ℝ) * p a) ≤ ∑ b ∈ t, (j b : ℝ) * q b := by
  classical
  have h := first_moment_le_of_tail_domination (s ×ˢ s) t
    (fun ab => i ab.1 + i ab.2) j (fun ab => p ab.1 * p ab.2) q N
    (by
      intro ab hab
      exact hi ab.1 (Finset.mem_product.mp hab).1 ab.2 (Finset.mem_product.mp hab).2)
    hj (by simpa only [Finset.sum_product] using htail)
  simpa only [Finset.sum_product, product_first_moment s i p hp] using h

section PositiveMatrixOverlap

open scoped ComplexOrder Matrix

/-- Positive semidefinite complex matrices have nonnegative real trace;
the inequality here uses the standard partial order on complex numbers. -/
theorem psd_trace_nonnegative {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) : 0 ≤ A.trace := by
  classical
  unfold Matrix.trace
  apply Finset.sum_nonneg
  intro i _
  simpa only [Matrix.mulVec_single_one, ← Pi.single_star, star_one,
    single_dotProduct, one_mul, Matrix.transpose_apply] using hA.2 (Pi.single i 1)

/-- The Hilbert--Schmidt overlap of two positive semidefinite complex
matrices is real and nonnegative, without a commutativity assumption. -/
theorem psd_trace_product_nonnegative {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨C, hC⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hB
  rw [hC, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact psd_trace_nonnegative _ (hA.mul_mul_conjTranspose_same C)

/-- Real/imaginary-part version of positive-matrix overlap positivity. -/
theorem psd_overlap_real_nonnegative {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace.im = 0 ∧ 0 ≤ (A * B).trace.re := by
  have h := RCLike.nonneg_iff.mp (psd_trace_product_nonnegative A B hA hB)
  exact ⟨h.2, h.1⟩

/-- Two positive matrices of equal positive Hilbert--Schmidt square have
normalized overlap in `[0,1]`. The upper bound follows from the nonnegative
Hilbert--Schmidt square of their difference. -/
theorem normalized_psd_overlap_bounds {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hP : 0 < (A * A).trace.re)
    (hsquare : (B * B).trace.re = (A * A).trace.re) :
    0 ≤ (A * B).trace.re / (A * A).trace.re ∧
      (A * B).trace.re / (A * A).trace.re ≤ 1 := by
  have hoverlap := (psd_overlap_real_nonnegative A B hA hB).2
  have hdiff := (RCLike.nonneg_iff.mp
    (psd_trace_nonnegative _ (Matrix.posSemidef_conjTranspose_mul_self (A - B)))).1
  have hgap : 0 ≤ (A * A).trace.re - (B * A).trace.re -
      ((A * B).trace.re - (B * B).trace.re) := by
    change 0 ≤ (((A - B)ᴴ * (A - B)).trace).re at hdiff
    simpa only [Matrix.conjTranspose_sub, hA.isHermitian.eq, hB.isHermitian.eq,
      sub_mul, mul_sub, Matrix.trace_sub, Complex.sub_re] using hdiff
  rw [Matrix.trace_mul_comm B A, hsquare] at hgap
  constructor
  · exact div_nonneg hoverlap hP.le
  · apply (div_le_one hP).mpr
    linarith

/-- Entrywise form of the squared Hilbert--Schmidt norm. -/
theorem trace_adjoint_mul_re {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) :
    (Aᴴ * A).trace.re = ∑ j, ∑ i, Complex.normSq (A i j) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ← Complex.normSq_eq_conj_mul_self]

/-- A nonzero Hermitian matrix has strictly positive Hilbert--Schmidt square. -/
theorem hermitian_trace_square_positive {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (hne : A ≠ 0) :
    0 < (A * A).trace.re := by
  classical
  have hentry : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (by ext i j; exact h i j)
  obtain ⟨i, j, hij⟩ := hentry
  have hsq : (A * A).trace.re = ∑ j, ∑ i, Complex.normSq (A i j) := by
    simpa only [hA.eq] using trace_adjoint_mul_re A
  rw [hsq]
  apply Finset.sum_pos'
  · intro k _
    exact Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro k _
      exact Complex.normSq_nonneg _
    · exact ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hij⟩

/-- Unit trace supplies the positive denominator used for a density seed. -/
theorem density_trace_square_positive {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (htrace : A.trace = 1) :
    0 < (A * A).trace.re := by
  apply hermitian_trace_square_positive A hA.isHermitian
  intro hzero
  simp [hzero] at htrace

/-- Unitary conjugation preserves the Hilbert--Schmidt square of a
Hermitian matrix. The trace identity itself does not need Hermiticity. -/
theorem trace_square_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) :
    ((U * A * Uᴴ) * (U * A * Uᴴ)).trace = (A * A).trace := by
  calc
    ((U * A * Uᴴ) * (U * A * Uᴴ)).trace =
        ((U * A * Uᴴ) * (U * A) * Uᴴ).trace := by
      simp only [Matrix.mul_assoc]
    _ = (Uᴴ * (U * A * Uᴴ) * (U * A)).trace :=
      Matrix.trace_mul_cycle _ _ _
    _ = ((Uᴴ * U) * A * (Uᴴ * U) * A).trace := by
      simp only [Matrix.mul_assoc]
    _ = (A * A).trace := by rw [hU]; simp

/-- The normalized return overlap under unitary conjugation is real,
nonnegative, and at most one. This applies to a positive mixed seed or its
positive square root, whenever its Hilbert--Schmidt square is nonzero. -/
theorem normalized_unitary_psd_overlap_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A U : Matrix ι ι ℂ) (hA : A.PosSemidef) (hU : Uᴴ * U = 1)
    (hP : 0 < (A * A).trace.re) :
    (A * (U * A * Uᴴ)).trace.im = 0 ∧
      0 ≤ (A * (U * A * Uᴴ)).trace.re / (A * A).trace.re ∧
      (A * (U * A * Uᴴ)).trace.re / (A * A).trace.re ≤ 1 := by
  have hB := hA.mul_mul_conjTranspose_same U
  refine ⟨(psd_overlap_real_nonnegative A _ hA hB).1, ?_⟩
  apply normalized_psd_overlap_bounds A _ hA hB hP
  rw [trace_square_conjugation A U hU]

/-- Combined return/loss corollary with the real normalized return amplitude
constructed from two positive matrices of equal Hilbert--Schmidt norm. -/
theorem finite_loss_bounds_of_psd_overlap {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hP : 0 < (A * A).trace.re)
    (hsquare : (B * B).trace.re = (A * A).trace.re)
    (N : ℕ) (p : Fin (N + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hreturn : p 0 = ((A * B).trace.re / (A * A).trace.re) ^ 2)
    (hN : N ≤ 4) :
    1 - (A * B).trace.re / (A * A).trace.re ≤ finiteComplexity N p ∧
      finiteComplexity N p ≤ 8 * (1 - (A * B).trace.re / (A * A).trace.re) := by
  obtain ⟨h0, h1⟩ := normalized_psd_overlap_bounds A B hA hB hP hsquare
  exact finite_loss_bounds N p hp hsum _ h0 h1 hreturn hN

end PositiveMatrixOverlap

section OrthogonalProjection

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Norm monotonicity for nested genuine orthogonal projections. -/
theorem nested_projection_norm_le (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : U ≤ V) (x : E) :
    ‖U.orthogonalProjection x‖ ≤ ‖V.orthogonalProjection x‖ := by
  rw [← Submodule.orthogonalProjection_orthogonalProjection_of_le hUV x]
  calc
    ‖U.orthogonalProjection (V.orthogonalProjection x : E)‖ ≤
        ‖U.orthogonalProjection‖ * ‖(V.orthogonalProjection x : E)‖ :=
      U.orthogonalProjection.le_opNorm _
    _ ≤ 1 * ‖(V.orthogonalProjection x : E)‖ :=
      mul_le_mul_of_nonneg_right (Submodule.orthogonalProjection_norm_le U) (norm_nonneg _)
    _ = ‖V.orthogonalProjection x‖ := by simp

/-- Nested projections imply the squared-norm tail comparison used by
finite Krylov-flag arguments. No probability identification is assumed. -/
theorem nested_projection_tail_le (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : U ≤ V) (x : E) (c : ℝ) :
    c - ‖V.orthogonalProjection x‖ ^ 2 ≤ c - ‖U.orthogonalProjection x‖ ^ 2 := by
  have h := nested_projection_norm_le U V hUV x
  nlinarith [norm_nonneg (U.orthogonalProjection x), norm_nonneg (V.orthogonalProjection x)]

/-- The difference between nested projection masses is exactly the squared
norm of the difference of their projected vectors. -/
theorem nested_projection_mass_gap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : U ≤ V) (x : E) :
    ‖V.orthogonalProjection x‖ ^ 2 - ‖U.orthogonalProjection x‖ ^ 2 =
      ‖(V.orthogonalProjection x : E) - (U.orthogonalProjection x : E)‖ ^ 2 := by
  have horth := Submodule.orthogonalProjection_inner_eq_zero (K := U)
    (V.orthogonalProjection x : E) (U.orthogonalProjection x : E)
    (U.orthogonalProjection x).property
  rw [Submodule.orthogonalProjection_orthogonalProjection_of_le hUV x] at horth
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    ((V.orthogonalProjection x : E) - (U.orthogonalProjection x : E))
    (U.orthogonalProjection x : E) horth
  simp only [sub_add_cancel, Submodule.coe_norm] at hpyth
  simp only [Submodule.coe_norm]
  nlinarith

/-- A geometric version of the factor-two implication. Actual nested
orthogonal projection flags supply the tail inequality, while the equalities
identifying their masses with the chosen distributions remain explicit.
No Hamiltonian, Krylov basis, or tensor flag is silently assumed. -/
theorem factor_two_of_nested_projection_flags {α β : Type*}
    (s : Finset α) (t : Finset β) (i : α → ℕ) (j : β → ℕ)
    (p : α → ℝ) (q : β → ℝ) (N : ℕ)
    (hp : ∑ a ∈ s, p a = 1)
    (hi : ∀ a ∈ s, ∀ b ∈ s, i a + i b ≤ N)
    (hj : ∀ b ∈ t, j b ≤ N)
    (U V : ℕ → Submodule 𝕜 E)
    [∀ n, (U n).HasOrthogonalProjection] [∀ n, (V n).HasOrthogonalProjection]
    (hUV : ∀ n < N, U n ≤ V n) (x : E)
    (hproduct : ∀ n < N,
      (∑ a ∈ s, ∑ b ∈ s, if n < i a + i b then p a * p b else 0) =
        1 - ‖(V n).orthogonalProjection x‖ ^ 2)
    (hoperator : ∀ n < N,
      (∑ b ∈ t, if n < j b then q b else 0) =
        1 - ‖(U n).orthogonalProjection x‖ ^ 2) :
    2 * (∑ a ∈ s, (i a : ℝ) * p a) ≤ ∑ b ∈ t, (j b : ℝ) * q b := by
  apply factor_two_of_tail_domination s t i j p q N hp hi hj
  intro n hn
  rw [hproduct n hn, hoperator n hn]
  exact nested_projection_tail_le (U n) (V n) (hUV n hn) x 1

/-- The exact finite projection-gap identity. Its explicit probability/flag
identifications are the hypotheses still needed to instantiate this for a
physical Krylov chain. -/
theorem factor_two_gap_of_nested_projection_flags {α β : Type*}
    (s : Finset α) (t : Finset β) (i : α → ℕ) (j : β → ℕ)
    (p : α → ℝ) (q : β → ℝ) (N : ℕ)
    (hp : ∑ a ∈ s, p a = 1)
    (hi : ∀ a ∈ s, ∀ b ∈ s, i a + i b ≤ N)
    (hj : ∀ b ∈ t, j b ≤ N)
    (U V : ℕ → Submodule 𝕜 E)
    [∀ n, (U n).HasOrthogonalProjection] [∀ n, (V n).HasOrthogonalProjection]
    (hUV : ∀ n < N, U n ≤ V n) (x : E)
    (hproduct : ∀ n < N,
      (∑ a ∈ s, ∑ b ∈ s, if n < i a + i b then p a * p b else 0) =
        1 - ‖(V n).orthogonalProjection x‖ ^ 2)
    (hoperator : ∀ n < N,
      (∑ b ∈ t, if n < j b then q b else 0) =
        1 - ‖(U n).orthogonalProjection x‖ ^ 2) :
    (∑ b ∈ t, (j b : ℝ) * q b) - 2 * (∑ a ∈ s, (i a : ℝ) * p a) =
      ∑ n ∈ Finset.range N,
        ‖((V n).orthogonalProjection x : E) - ((U n).orthogonalProjection x : E)‖ ^ 2 := by
  rw [← finite_tail_sum t j q N hj, ← product_finite_tail_sum s i p N hp hi,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_range.mp hn
  rw [hoperator n hn', hproduct n hn']
  have hgap := nested_projection_mass_gap (U n) (V n) (hUV n hn') x
  linarith

end OrthogonalProjection

end Krylov
