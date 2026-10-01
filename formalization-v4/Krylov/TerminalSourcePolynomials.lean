import Krylov.WitnessSourceAPI

namespace Krylov.TerminalSourcePolynomials
open Matrix Polynomial OperatorBridge UnitaryCovariance GSUnitaryTransport
noncomputable section
set_option maxHeartbeats 1000000

theorem mixed_terminal :
    (Polynomial.aeval (FactorTwo.commutator (States.hR.map Complex.ofReal)))
      (X*(X-C 2)*(X+C 2) : Polynomial ℂ) (States.rhoR.map Complex.ofReal) = 0 := by
  apply (matrixChange rightBasis rightBasis_unitary rightBasis_unitary_reverse).injective
  change changeBasis rightBasis _ = changeBasis rightBasis 0
  rw [polynomial_change _ _ _ rightBasis_unitary_reverse,
    right_hamiltonian_coordinates,right_density_coordinates,MatrixGSBridge.diagonal_commutator]
  simp only [changeBasis,mul_zero,zero_mul]
  ext i j
  rw [polynomial_liouvillian_entry]
  fin_cases i <;> fin_cases j <;>
    norm_num [ConcreteChains.RightMixed.seed,States.rhoRE,States.energyR]

theorem purified_terminal :
    (Polynomial.aeval (FactorTwo.commutator PurifiedCovariance.originalGenerator))
      (X*(X-C 2)*(X-C 1)*(X+C 1)*(X+C 2) : Polynomial ℂ) PurifiedCovariance.originalSeed = 0 := by
  apply (matrixChange PurifiedCovariance.basis PurifiedCovariance.basis_unitary
    PurifiedCovariance.basis_unitary_reverse).injective
  change changeBasis PurifiedCovariance.basis _ = changeBasis PurifiedCovariance.basis 0
  rw [polynomial_change _ _ _ PurifiedCovariance.basis_unitary_reverse,
    PurifiedCovariance.generator_coordinates,PurifiedCovariance.seed_coordinates,
    MatrixGSBridge.diagonal_commutator]
  simp only [changeBasis,mul_zero,zero_mul]
  ext ⟨i,j⟩ ⟨k,l⟩
  rw [polynomial_liouvillian_entry]
  have hp : (X*(X-C 2)*(X-C 1)*(X+C 1)*(X+C 2) : Polynomial ℂ).eval
      ((PurifiedChain.energies (i,j)-PurifiedChain.energies (k,l) : ℝ) : ℂ)=0 := by
    fin_cases i <;> fin_cases k <;> norm_num [PurifiedChain.energies,States.energyR]
  rw [hp,zero_mul]
  rfl

end
end Krylov.TerminalSourcePolynomials
