import Mathlib

/-! Difference-convolution measure of the actual rank-one purified seed.
Indices `(i,j)` implement row vectorization. This file supplies the algebraic
pure-density bridge without assuming a probability convolution as an axiom. -/
namespace Krylov.Purification
open scoped BigOperators
open Matrix
noncomputable section

variable {n : ℕ}

def rowWeight (S : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ :=
  ∑ j, Complex.normSq (S i j)

def pureSeed (S : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun a b => S a.1 a.2 * star (S b.1 b.2)

def pureGapWeight (E : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℂ) (ω : ℝ) : ℝ :=
  ∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
    if E a.1 - E b.1 = ω then Complex.normSq (pureSeed S a b) else 0

theorem pureSeed_norm (S : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n × Fin n) :
    Complex.normSq (pureSeed S a b) =
      Complex.normSq (S a.1 a.2) * Complex.normSq (S b.1 b.2) := by
  simp [pureSeed, map_mul]

theorem rowWeight_eq_density_diagonal (S : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    rowWeight S i = ((S * Sᴴ) i i).re := by
  simp [rowWeight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, ← Complex.ofReal_sum]

theorem pure_gap_difference_convolution (E : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℂ) (ω : ℝ) :
    pureGapWeight E S ω =
      ∑ i, ∑ k, if E i - E k = ω then rowWeight S i * rowWeight S k else 0 := by
  simp only [pureGapWeight, Fintype.sum_prod_type, pureSeed_norm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : E i - E k = ω
  · simp only [h, ↓reduceIte, rowWeight]
    rw [Finset.sum_mul_sum]
  · simp [h]

theorem rowWeight_nonnegative (S : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    0 ≤ rowWeight S i := by
  exact Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)

theorem pureSeed_hsNorm (S : Matrix (Fin n) (Fin n) ℂ) :
    (∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n, Complex.normSq (pureSeed S a b)) =
      (∑ i, rowWeight S i)^2 := by
  simp only [pureSeed_norm, Fintype.sum_prod_type, rowWeight]
  simp only [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem normalized_pureSeed (S : Matrix (Fin n) (Fin n) ℂ)
    (h : ∑ i, rowWeight S i = 1) :
    (∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n, Complex.normSq (pureSeed S a b)) = 1 := by
  rw [pureSeed_hsNorm, h]; norm_num

/-- The actual lifted generator `diag(E) ⊗ I` in row-vectorized coordinates. -/
def liftedGenerator (E : Fin n → ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  Matrix.diagonal (fun a => (E a.1 : ℂ))

theorem lifted_commutator_entry (E : Fin n → ℝ)
    (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (a b : Fin n × Fin n) :
    (liftedGenerator E * A - A * liftedGenerator E) a b =
      ((E a.1 : ℂ) - (E b.1 : ℂ)) * A a b := by
  simp [liftedGenerator, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring
end
end Krylov.Purification
