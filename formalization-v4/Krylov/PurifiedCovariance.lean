import Krylov.PurifiedChain
import Krylov.UnitaryCovariance

/-! Original-basis transport for the rank-one purified right witness. -/
namespace Krylov.PurifiedCovariance
open Matrix OperatorBridge UnitaryCovariance
open scoped BigOperators Kronecker
noncomputable section

variable {n : ℕ}

def lift (A : Operator (Fin n)) : Operator (Fin n × Fin n) :=
  A ⊗ₖ (1 : Operator (Fin n))

theorem lift_adjoint (A : Operator (Fin n)) : (lift A)ᴴ = lift Aᴴ := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases h : j=l <;> simp [lift, kronecker_apply, conjTranspose_apply, Matrix.one_apply, Complex.star_def, h, eq_comm]

theorem lift_mul (A B : Operator (Fin n)) : lift (A*B) = lift A * lift B := by
  unfold lift
  rw [← Matrix.mul_kronecker_mul, one_mul]

theorem lift_one : lift (1 : Operator (Fin n)) = 1 := Matrix.one_kronecker_one

theorem lift_changeBasis (Q A : Operator (Fin n)) :
    changeBasis (lift Q) (lift A) = lift (changeBasis Q A) := by
  simp only [changeBasis, lift_adjoint, ← lift_mul]

theorem lift_unitary (Q : Operator (Fin n)) (hQ : Qᴴ * Q = 1) :
    (lift Q)ᴴ * lift Q = 1 := by
  rw [lift_adjoint, ← lift_mul, hQ, lift_one]

theorem lift_unitary_reverse (Q : Operator (Fin n)) (hQ : Q * Qᴴ = 1) :
    lift Q * (lift Q)ᴴ = 1 := by
  rw [lift_adjoint, ← lift_mul, hQ, lift_one]

theorem lift_diagonal (E : Fin n → ℝ) :
    lift (hamiltonian E) = hamiltonian (fun a : Fin n × Fin n => E a.1) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases hi : i=k <;> by_cases hj : j=l <;>
    simp [lift, hamiltonian, kronecker_apply, Matrix.diagonal, Matrix.one_apply, hi, hj]

/-- Row-vectorized pure-density conjugation acts on the physical factor only. -/
theorem pureSeed_changeBasis (Q S : Operator (Fin n)) :
    changeBasis (lift Q) (Purification.pureSeed S) = Purification.pureSeed (Qᴴ * S) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [changeBasis, lift, Purification.pureSeed, mul_apply, conjTranspose_apply,
    kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul,
    Complex.star_def, map_sum, map_mul, apply_ite, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

def originalRoot : Operator (Fin 3) := States.rootR.map Complex.ofReal

def originalSeed : Operator PurifiedChain.Index := Purification.pureSeed originalRoot

def originalGenerator : Operator PurifiedChain.Index := lift (States.hR.map Complex.ofReal)

def basis : Operator PurifiedChain.Index := lift rightBasis

def originalChain (k : Fin 5) : Operator PurifiedChain.Index :=
  changeBasis basisᴴ (PurifiedChain.chain k)

theorem basis_unitary : basisᴴ * basis = 1 := lift_unitary _ rightBasis_unitary

theorem basis_unitary_reverse : basis * basisᴴ = 1 := lift_unitary_reverse _ rightBasis_unitary_reverse

theorem original_root_coordinates : rightBasisᴴ * originalRoot = PurifiedChain.squareRootInEnergyBasis := by
  unfold rightBasis originalRoot PurifiedChain.squareRootInEnergyBasis
  rw [← complexify_transpose, ← complexify_mul]

theorem generator_coordinates : changeBasis basis originalGenerator = hamiltonian PurifiedChain.energies := by
  unfold basis originalGenerator
  rw [lift_changeBasis, right_hamiltonian_coordinates, lift_diagonal]
  rfl

theorem seed_coordinates : changeBasis basis originalSeed = PurifiedChain.seed := by
  unfold basis originalSeed
  rw [pureSeed_changeBasis, original_root_coordinates]
  rfl

theorem original_probability (k : Fin 5) (t : ℝ) :
    matrixProbability originalGenerator originalSeed (originalChain k) t =
      PurifiedChain.chainProbability k t := by
  rw [← matrixProbability_changeBasis basis _ _ _ t basis_unitary basis_unitary_reverse]
  rw [generator_coordinates, seed_coordinates, originalChain,
    changeBasis_inverse _ _ basis_unitary, diagonal_probability]
  rfl

theorem original_complexity :
    (∑ k : Fin 5, (k.val : ℝ) * matrixProbability originalGenerator originalSeed
      (originalChain k) (Real.pi/3)) = 2967537/2456246 := by
  simp_rw [original_probability]
  exact PurifiedChain.exact_complexity

theorem original_right_gap :
    (∑ k : Fin 3, (k.val : ℝ) * matrixProbability (States.hR.map Complex.ofReal)
      (States.rhoR.map Complex.ofReal) (rightOriginalChain k) (Real.pi/3)) -
    (∑ k : Fin 5, (k.val : ℝ) * matrixProbability originalGenerator originalSeed
      (originalChain k) (Real.pi/3)) = 1600683/39299936 := by
  rw [right_original_complexity, original_complexity]; norm_num

theorem original_right_violation :
    (∑ k : Fin 5, (k.val : ℝ) * matrixProbability originalGenerator originalSeed
      (originalChain k) (Real.pi/3)) <
    (∑ k : Fin 3, (k.val : ℝ) * matrixProbability (States.hR.map Complex.ofReal)
      (States.rhoR.map Complex.ofReal) (rightOriginalChain k) (Real.pi/3)) := by
  rw [right_original_complexity, original_complexity]; norm_num

end
end Krylov.PurifiedCovariance
