import Mathlib

/-!
Concrete physical-input certificates for the two qutrit witnesses.  Matrices
are real symmetric, hence also give Hermitian physical matrices after scalar
extension to complex numbers.  `PosDef`, trace, matrix multiplication, and the
energy-basis transformation below are mathlib notions.  The finite gap sums
are the entrywise spectral weights of the diagonal commutator, whose action
is proved explicitly here.  No general Krylov/spectral representation theorem
is asserted in this file.
-/
namespace Krylov.States
open Matrix
open scoped BigOperators

abbrev Qutrit := Matrix (Fin 3) (Fin 3) ℝ

noncomputable def rhoL : Qutrit :=
  !![32/42, 0, 0; 0, 5/42, 3/42; 0, 3/42, 5/42]
noncomputable def hL : Qutrit := diagonal ![2,0,1]
noncomputable def rhoR : Qutrit := diagonal ![16/26,1/26,9/26]
noncomputable def hR : Qutrit := !![0,1,0;1,0,0;0,0,0]

theorem rhoL_hermitian : rhoL.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [rhoL, IsHermitian, conjTranspose_apply]
theorem rhoR_hermitian : rhoR.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [rhoR, IsHermitian, conjTranspose_apply, diagonal]
theorem hL_hermitian : hL.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [hL, IsHermitian, conjTranspose_apply, diagonal]
theorem hR_hermitian : hR.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [hR, IsHermitian, conjTranspose_apply]

theorem rhoL_trace : trace rhoL = 1 := by
  norm_num [trace, rhoL, Fin.sum_univ_succ]
theorem rhoR_trace : trace rhoR = 1 := by
  norm_num [trace, rhoR, Fin.sum_univ_succ]
theorem rhoL_purity : trace (rhoL * rhoL) = 13/21 := by
  norm_num [trace, mul_apply, rhoL, Fin.sum_univ_succ]
theorem rhoR_purity : trace (rhoR * rhoR) = 1/2 := by
  norm_num [trace, mul_apply, rhoR, Fin.sum_univ_succ]

private theorem coordinates_sq_pos (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  have hn0 := sq_nonneg (x 0)
  have hn1 := sq_nonneg (x 1)
  have hn2 := sq_nonneg (x 2)
  by_contra hp
  have h0 : x 0 = 0 := by nlinarith
  have h1 : x 1 = 0 := by nlinarith
  have h2 : x 2 = 0 := by nlinarith
  apply hx
  ext i; fin_cases i <;> simp_all

theorem rhoL_posDef : rhoL.PosDef := by
  refine ⟨rhoL_hermitian, ?_⟩
  intro x hx
  have hp := coordinates_sq_pos x hx
  have hn := sq_nonneg (x 1 + x 2)
  have hn0 := sq_nonneg (x 0)
  norm_num [dotProduct, mulVec, rhoL, Fin.sum_univ_succ]
  nlinarith

theorem rhoR_posDef : rhoR.PosDef := by
  apply PosDef.diagonal
  intro i; fin_cases i <;> norm_num

theorem rhoL_full_rank : IsUnit rhoL := rhoL_posDef.isUnit
theorem rhoR_full_rank : IsUnit rhoR := rhoR_posDef.isUnit

noncomputable def sL : ℝ := Real.sqrt 21 / 42
noncomputable def rootL : Qutrit :=
  !![8*sL,0,0;0,3*sL,sL;0,sL,3*sL]
noncomputable def sR : ℝ := Real.sqrt 26 / 26
noncomputable def rootR : Qutrit := diagonal ![4*sR,sR,3*sR]

theorem sL_pos : 0 < sL := by unfold sL; positivity
theorem sR_pos : 0 < sR := by unfold sR; positivity
theorem sL_sq : sL ^ 2 = 1/84 := by
  dsimp [sL]; rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)]; norm_num
theorem sR_sq : sR ^ 2 = 1/26 := by
  dsimp [sR]; rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 26)]; norm_num

theorem rootL_square : rootL * rootL = rhoL := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [rootL, rhoL, mul_apply, diagonal, Fin.sum_univ_succ] <;> nlinarith [sL_sq]
theorem rootR_square : rootR * rootR = rhoR := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [rootR, rhoR, mul_apply, diagonal, Fin.sum_univ_succ] <;> nlinarith [sR_sq]

theorem rootL_hermitian : rootL.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [rootL, IsHermitian, conjTranspose_apply]
theorem rootL_posDef : rootL.PosDef := by
  refine ⟨rootL_hermitian, ?_⟩
  intro x hx
  have hp := coordinates_sq_pos x hx
  have hn := sq_nonneg (x 1 + x 2)
  have hn0 := sq_nonneg (x 0)
  have hq : 0 < 8 * x 0 ^ 2 + 3 * x 1 ^ 2 + 2 * x 1 * x 2 + 3 * x 2 ^ 2 := by
    nlinarith
  have hprod := mul_pos sL_pos hq
  norm_num [dotProduct, mulVec, rootL, Fin.sum_univ_succ]
  nlinarith

theorem rootR_posDef : rootR.PosDef := by
  apply PosDef.diagonal
  intro i; fin_cases i <;> norm_num [sR]

theorem rootL_is_positive_square_root : rootL = rhoL_posDef.posSemidef.sqrt := by
  exact rootL_posDef.posSemidef.eq_sqrt_of_sq_eq rhoL_posDef.posSemidef
    (by simpa only [pow_two] using rootL_square)
theorem rootR_is_positive_square_root : rootR = rhoR_posDef.posSemidef.sqrt := by
  exact rootR_posDef.posSemidef.eq_sqrt_of_sq_eq rhoR_posDef.posSemidef
    (by simpa only [pow_two] using rootR_square)

/-! Orthogonal diagonalization of the right Hamiltonian, ordered as -1,0,1. -/
noncomputable def q : ℝ := Real.sqrt 2 / 2
noncomputable def energyBasisR : Qutrit := !![q,0,q;-q,0,q;0,1,0]
noncomputable def energyR : Fin 3 → ℝ := ![-1,0,1]
noncomputable def rhoRE : Qutrit := !![17/52,0,15/52;0,9/26,0;15/52,0,17/52]

theorem q_sq : q ^ 2 = 1/2 := by
  dsimp [q]; rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

theorem energyBasisR_orthogonal : energyBasisRᵀ * energyBasisR = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [energyBasisR, mul_apply, diagonal, Fin.sum_univ_succ] <;> nlinarith [q_sq]
theorem energyBasisR_orthogonal_reverse : energyBasisR * energyBasisRᵀ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [energyBasisR, mul_apply, diagonal, Fin.sum_univ_succ] <;> nlinarith [q_sq]
theorem hR_energy_basis : energyBasisRᵀ * hR * energyBasisR = diagonal energyR := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [energyBasisR, hR, energyR, mul_apply, diagonal, Fin.sum_univ_succ] <;> nlinarith [q_sq]
theorem rhoR_energy_basis : energyBasisRᵀ * rhoR * energyBasisR = rhoRE := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [energyBasisR, rhoR, rhoRE, mul_apply, diagonal, Fin.sum_univ_succ] <;> nlinarith [q_sq]

noncomputable def stateBasisL : Qutrit := !![1,0,0;0,q,q;0,q,-q]
theorem stateBasisL_orthogonal : stateBasisLᵀ * stateBasisL = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [stateBasisL, mul_apply, diagonal, Fin.sum_univ_succ] <;> nlinarith [q_sq]
theorem rhoL_diagonalization : stateBasisLᵀ * rhoL * stateBasisL =
    diagonal ![16/21,4/21,1/21] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [stateBasisL, rhoL, mul_apply, diagonal, Fin.sum_univ_succ] <;> nlinarith [q_sq]

/-! Entrywise diagonalization of the commutator and exact finite spectral sums. -/
theorem diagonal_commutator_entry {n : ℕ} (E : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (diagonal E * A - A * diagonal E) i j = (E i - E j) * A i j := by
  simp [sub_mul]; ring

/-- The Euclidean norm of vectorized real matrices is the Hilbert--Schmidt norm. -/
def hsNormSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ a, ∑ b, (A a b)^2

theorem hsNormSq_eq_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    hsNormSq A = trace (Aᵀ * A) := by
  simp only [hsNormSq, trace, mul_apply, transpose_apply, pow_two]
  exact Finset.sum_comm

theorem rootL_normalized : hsNormSq rootL = 1 := by
  rw [hsNormSq_eq_trace]
  have ht : rootLᵀ = rootL := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rootL]
  rw [ht, rootL_square, rhoL_trace]
theorem rootR_normalized : hsNormSq rootR = 1 := by
  rw [hsNormSq_eq_trace]
  have ht : rootRᵀ = rootR := diagonal_transpose _
  rw [ht, rootR_square, rhoR_trace]

noncomputable def gapWeight {n : ℕ} (E : Fin n → ℝ)
    (w : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) : ℝ :=
  ∑ a, ∑ b, if E a - E b = ω then w a b else 0
noncomputable def operatorGapWeight {n : ℕ} (E : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) : ℝ :=
  gapWeight E (fun a b => (A a b)^2) ω
noncomputable def pureGapWeight {n : ℕ} (E p : Fin n → ℝ) (ω : ℝ) : ℝ :=
  gapWeight E (fun a b => p a * p b) ω

/-- Orthogonal projection onto a gap eigenspace, in entry coordinates. -/
noncomputable def gapProjection {n : ℕ} (E : Fin n → ℝ) (ω : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => if E a - E b = ω then A a b else 0

theorem gapProjection_eigenvector {n : ℕ} (E : Fin n → ℝ) (ω : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    diagonal E * gapProjection E ω A - gapProjection E ω A * diagonal E =
      ω • gapProjection E ω A := by
  ext i j
  rw [diagonal_commutator_entry]
  by_cases h : E i - E j = ω <;> simp [gapProjection, h]

theorem gapProjection_weight {n : ℕ} (E : Fin n → ℝ) (ω : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    hsNormSq (gapProjection E ω A) = operatorGapWeight E A ω := by
  unfold hsNormSq operatorGapWeight gapWeight gapProjection
  congr 1; ext a; congr 1; ext b
  split_ifs <;> simp

/-- Distinct gap projections are orthogonal for the real Hilbert--Schmidt product. -/
theorem gapProjection_orthogonal {n : ℕ} (E : Fin n → ℝ) (ω ν : ℝ)
    (A B : Matrix (Fin n) (Fin n) ℝ) (hne : ω ≠ ν) :
    ∑ a, ∑ b, gapProjection E ω A a b * gapProjection E ν B a b = 0 := by
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  by_cases hω : E a - E b = ω
  · have hν : E a - E b ≠ ν := by intro h; exact hne (hω.symm.trans h)
    simp [gapProjection, hω, hν, hne]
  · simp [gapProjection, hω]

/-- A complete finite spectral decomposition of the commutator seed. -/
theorem gapProjection_complete {n : ℕ} (E : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset ℝ)
    (hS : ∀ a b, E a - E b ∈ S) :
    ∑ ω ∈ S, gapProjection E ω A = A := by
  classical
  ext a b
  simp [Matrix.sum_apply, gapProjection, Finset.sum_ite_eq, hS]

noncomputable def energyL : Fin 3 → ℝ := ![2,0,1]
noncomputable def leftNodes : Fin 3 → ℝ := ![-1,0,1]
noncomputable def rightMixedNodes : Fin 3 → ℝ := ![-2,0,2]
noncomputable def rightPurifiedNodes : Fin 5 → ℝ := ![-2,-1,0,1,2]
noncomputable def rightEnergyWeights : Fin 3 → ℝ := ![17/52,9/26,17/52]

theorem rhoRE_diagonal : ∀ i, rhoRE i i = rightEnergyWeights i := by
  intro i; fin_cases i <;> norm_num [rhoRE, rightEnergyWeights]
theorem rightEnergyWeights_normalized : ∑ i, rightEnergyWeights i = 1 := by
  norm_num [rightEnergyWeights, Fin.sum_univ_succ]

theorem left_mixed_gap_weights : ∀ i,
    operatorGapWeight energyL rhoL (leftNodes i) / trace (rhoL * rhoL) =
      (![3/364,179/182,3/364] : Fin 3 → ℝ) i := by
  intro i; fin_cases i <;>
    norm_num [operatorGapWeight, gapWeight, energyL, rhoL, leftNodes,
      rhoL_purity, Fin.sum_univ_succ]
theorem left_spread_gap_weights : ∀ i,
    operatorGapWeight energyL rootL (leftNodes i) =
      (![1/84,41/42,1/84] : Fin 3 → ℝ) i := by
  intro i; fin_cases i <;>
    norm_num [operatorGapWeight, gapWeight, energyL, rootL, leftNodes,
      Fin.sum_univ_succ] <;> nlinarith [sL_sq]
theorem right_mixed_gap_weights : ∀ i,
    operatorGapWeight energyR rhoRE (rightMixedNodes i) / trace (rhoR * rhoR) =
      (![225/1352,451/676,225/1352] : Fin 3 → ℝ) i := by
  intro i; fin_cases i <;>
    norm_num [operatorGapWeight, gapWeight, energyR, rhoRE, rightMixedNodes,
      rhoR_purity, Fin.sum_univ_succ]
theorem right_purified_gap_weights : ∀ i,
    pureGapWeight energyR (fun a => rhoRE a a) (rightPurifiedNodes i) =
      (![289/2704,153/676,451/1352,153/676,289/2704] : Fin 5 → ℝ) i := by
  intro i; fin_cases i <;>
    norm_num [pureGapWeight, gapWeight, energyR, rhoRE, rightPurifiedNodes,
      Fin.sum_univ_succ]

theorem left_mixed_no_other_gaps (ω : ℝ) (hm : ω ≠ -1) (hz : ω ≠ 0)
    (hp : ω ≠ 1) : operatorGapWeight energyL rhoL ω = 0 := by
  simp [operatorGapWeight, gapWeight, energyL, rhoL, Fin.sum_univ_succ,
    Ne.symm hm, Ne.symm hz, Ne.symm hp]
theorem left_spread_no_other_gaps (ω : ℝ) (hm : ω ≠ -1) (hz : ω ≠ 0)
    (hp : ω ≠ 1) : operatorGapWeight energyL rootL ω = 0 := by
  simp [operatorGapWeight, gapWeight, energyL, rootL, Fin.sum_univ_succ,
    Ne.symm hm, Ne.symm hz, Ne.symm hp]
theorem right_mixed_no_other_gaps (ω : ℝ) (hm : ω ≠ -2) (hz : ω ≠ 0)
    (hp : ω ≠ 2) : operatorGapWeight energyR rhoRE ω = 0 := by
  norm_num [operatorGapWeight, gapWeight, energyR, rhoRE, Fin.sum_univ_succ,
    Ne.symm hm, Ne.symm hz, Ne.symm hp]
theorem right_purified_no_other_gaps (ω : ℝ) (hm2 : ω ≠ -2) (hm1 : ω ≠ -1)
    (hz : ω ≠ 0) (hp1 : ω ≠ 1) (hp2 : ω ≠ 2) :
    pureGapWeight energyR (fun a => rhoRE a a) ω = 0 := by
  norm_num [pureGapWeight, gapWeight, energyR, rhoRE, Fin.sum_univ_succ,
    Ne.symm hm2, Ne.symm hm1, Ne.symm hz, Ne.symm hp1, Ne.symm hp2]

end Krylov.States
