import Mathlib

/-! Unitarity and actual Euclidean norm preservation for Hermitian Hamiltonian
matrix exponentials, without an assumed unitary-evolution hypothesis. -/
namespace Krylov.UnitaryEvolution
open Matrix
open scoped InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Operator (ι : Type*) := Matrix ι ι ℂ

def propagator (G : Operator ι) (t : ℝ) : Operator ι :=
  NormedSpace.exp ℂ ((-((t : ℂ) * Complex.I)) • G)

def hilbertVector (ψ : ι → ℂ) : EuclideanSpace ℂ ι :=
  (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm ψ

def evolvedVector (G : Operator ι) (ψ : ι → ℂ) (t : ℝ) : EuclideanSpace ℂ ι :=
  hilbertVector (propagator G t *ᵥ ψ)

theorem exponent_skewAdjoint (G : Operator ι) (hG : G.IsHermitian) (t : ℝ) :
    (((-((t : ℂ) * Complex.I)) • G) : Operator ι)ᴴ =
      -((-((t : ℂ) * Complex.I)) • G) := by
  have hc : star (-((t : ℂ) * Complex.I)) = -(-((t : ℂ) * Complex.I)) := by
    simp [Complex.star_def]
  rw [Matrix.conjTranspose_smul, hG.eq, hc]
  simp

/-- Actual matrix-exponential unitarity, proved on both sides. -/
theorem propagator_unitary (G : Operator ι) (hG : G.IsHermitian) (t : ℝ) :
    (propagator G t)ᴴ * propagator G t = 1 ∧
      propagator G t * (propagator G t)ᴴ = 1 := by
  let A : Operator ι := (-((t : ℂ) * Complex.I)) • G
  have hA : Aᴴ = -A := exponent_skewAdjoint G hG t
  unfold propagator
  change (NormedSpace.exp ℂ A)ᴴ * NormedSpace.exp ℂ A = 1 ∧
    NormedSpace.exp ℂ A * (NormedSpace.exp ℂ A)ᴴ = 1
  rw [← Matrix.exp_conjTranspose ℂ A, hA]
  constructor
  · rw [← Matrix.exp_add_of_commute ℂ (-A) A (Commute.neg_left (Commute.refl A))]
    simp
  · rw [← Matrix.exp_add_of_commute ℂ A (-A) (Commute.neg_right (Commute.refl A))]
    simp

/-- A matrix satisfying `UᴴU=1` preserves the actual Euclidean inner product. -/
theorem unitary_inner (U : Operator ι) (hU : Uᴴ * U = 1) (ψ φ : ι → ℂ) :
    ⟪hilbertVector (U *ᵥ ψ), hilbertVector (U *ᵥ φ)⟫_ℂ =
      ⟪hilbertVector ψ, hilbertVector φ⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (U *ᵥ φ) ⬝ᵥ star (U *ᵥ ψ) = φ ⬝ᵥ star ψ
  rw [dotProduct_comm (U *ᵥ φ), star_mulVec, dotProduct_mulVec, vecMul_vecMul, hU]
  simp [dotProduct_comm]

theorem unitary_norm (U : Operator ι) (hU : Uᴴ * U = 1) (ψ : ι → ℂ) :
    ‖hilbertVector (U *ᵥ ψ)‖ = ‖hilbertVector ψ‖ := by
  have hsq : ‖hilbertVector (U *ᵥ ψ)‖ ^ 2 = ‖hilbertVector ψ‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, unitary_inner U hU]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Norm preservation is supplied by the actual Hermitian Hamiltonian, for
all real times and without any spectral nondegeneracy assumption. -/
theorem evolvedVector_norm (G : Operator ι) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (t : ℝ) : ‖evolvedVector G ψ t‖ = ‖hilbertVector ψ‖ :=
  unitary_norm _ (propagator_unitary G hG t).1 ψ

theorem evolvedVector_unit (G : Operator ι) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (hψ : ‖hilbertVector ψ‖ = 1) (t : ℝ) :
    ‖evolvedVector G ψ t‖ = 1 := by
  rw [evolvedVector_norm G hG ψ t, hψ]

end
end Krylov.UnitaryEvolution
