import Krylov.OperatorBridge

/-! Row vectorization is a Hilbert--Schmidt isometry, and carries the
diagonal commutator to the purification difference generator. -/
namespace Krylov.Vectorization
open Matrix OperatorBridge
open scoped BigOperators ComplexConjugate
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rowVec (A : Operator ι) : EuclideanSpace ℂ (ι × ι) :=
  (WithLp.equiv 2 (ι × ι → ℂ)).symm (fun a => A a.1 a.2)

theorem rowVec_inner (A B : Operator ι) :
    inner (𝕜 := ℂ) (rowVec A) (rowVec B) = hsInner A B := by
  simp [rowVec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    hsInner, Fintype.sum_prod_type, mul_comm]

theorem rowVec_normSq (A : Operator ι) :
    ‖rowVec A‖^2 = (hsInner A A).re := by
  rw [← rowVec_inner, inner_self_eq_norm_sq_to_K]
  norm_cast

def differenceGenerator (E : ι → ℝ) : Matrix (ι × ι) (ι × ι) ℂ :=
  diagonal (fun a => ((E a.1-E a.2 : ℝ) : ℂ))

theorem rowVec_commutator (E : ι → ℝ) (A : Operator ι) :
    (rowVec (liouvillian E A) : ι × ι → ℂ) =
      differenceGenerator E *ᵥ (rowVec A : ι × ι → ℂ) := by
  funext a
  simp [rowVec, liouvillian, differenceGenerator, Matrix.mulVec_diagonal]

/-- Exact time evolution in vectorized coordinates, using actual scalar
phases and the actual commutator unitary evolution. -/
theorem rowVec_evolution (E : ι → ℝ) (A : Operator ι) (t : ℝ) :
    (rowVec (diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ) : ι × ι → ℂ) =
      diagonalUnitary (fun a : ι × ι => E a.1-E a.2) t *ᵥ
        (rowVec A : ι × ι → ℂ) := by
  rw [diagonalUnitary_conjugation]
  funext a
  simp [rowVec, spectralFilter, diagonalUnitary, Matrix.mulVec_diagonal]

end
end Krylov.Vectorization
