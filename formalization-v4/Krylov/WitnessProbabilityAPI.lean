import Krylov.CertifiedProbabilities
import Krylov.WitnessSourceAPI

namespace Krylov.WitnessProbabilityAPI
open Matrix OperatorBridge ConcreteChains UnitaryCovariance MatrixGSBridge WitnessSourceAPI
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option maxHeartbeats 2000000

abbrev degreeProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H A : Operator ι) (n : ℕ) (t : ℝ) : ℝ :=
  ‖⟪gramSchmidtNormed ℂ
      (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H)
        (PhysicalCurvatureNecessary.normalizedSeed A)) n,
    TaylorRemainder.evolution (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian H))
      (PhysicalCurvatureNecessary.normalizedSeed A) t⟫_ℂ‖^2

theorem diagonal_probability {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (E : ι → ℝ) (A : Operator ι) (hA : A ≠ 0)
    (v : Fin d → Operator ι) (p : Fin d → Polynomial ℂ)
    (hp : ∀ i, v i=(Polynomial.aeval (OperatorBridge.liouvillian E)) (p i) A)
    (hd : ∀ i, (p i).degree=(i.val : WithBot ℕ))
    (ho : Pairwise (fun i j => hsInner (v i) (v j)=0)) (i : Fin d) (t : ℝ) :
    degreeProbability (hamiltonian E) A i.val t = chainProbability E A (v i) t := by
  exact (CertifiedProbabilities.actual_probability (hamiltonian E) A (diagonal_hermitian E)
    hA v p (by simpa only [diagonal_commutator] using hp) hd ho i t).trans
      (UnitaryCovariance.diagonal_probability E A (v i) t)

lemma degreeProbability_changeBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q H A : Operator ι) (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1)
    (hH : H.IsHermitian) (n : ℕ) (t : ℝ) :
    degreeProbability (changeBasis Q H) (changeBasis Q A) n t =
      degreeProbability H A n t :=
  GSUnitaryTransport.probability_changeBasis Q H A hQ hQ' hH n t

theorem left_mixed (i : Fin 3) :
    degreeProbability (States.hL.map Complex.ofReal) (States.rhoL.map Complex.ofReal)
      i.val Real.pi = Spectral.LeftMixed.probabilities i := by
  rw [left_hamiltonian]
  change degreeProbability (hamiltonian States.energyL) LeftMixed.seed _ _ = _
  rw [diagonal_probability _ _
    (by simpa [LeftMixed.chain_zero] using LeftMixed.chain_nonzero 0)
    LeftMixed.chain LeftMixed.polynomial (fun _ => rfl)
    (by simpa [LeftMixed.polynomial,ThreeAtomOperator.polynomial] using
      CertifiedPolynomialDegrees.three (3/182))
    (by intro i j hij; simp [LeftMixed.gram,hij])]
  exact LeftMixed.exact_probabilities i

theorem left_spread (i : Fin 3) :
    degreeProbability (States.hL.map Complex.ofReal)
      complex_rhoL_posDef.posSemidef.sqrt i.val Real.pi = Spectral.LeftSpread.probabilities i := by
  rw [← complex_rootL_canonical,left_hamiltonian]
  change degreeProbability (hamiltonian States.energyL) LeftSpread.seed _ _ = _
  rw [diagonal_probability _ _
    (by simpa [LeftSpread.chain_zero] using LeftSpread.chain_nonzero 0)
    LeftSpread.chain LeftSpread.polynomial (fun _ => rfl)
    (by simpa [LeftSpread.polynomial,ThreeAtomOperator.polynomial] using
      CertifiedPolynomialDegrees.three (1/42))
    (by intro i j hij; simp [LeftSpread.gram,hij])]
  exact LeftSpread.exact_probabilities i

theorem right_mixed (i : Fin 3) :
    degreeProbability (States.hR.map Complex.ofReal) (States.rhoR.map Complex.ofReal)
      i.val (Real.pi/3) = Spectral.RightMixed.probabilities i := by
  rw [← degreeProbability_changeBasis rightBasis _ _ rightBasis_unitary
    rightBasis_unitary_reverse right_hermitian,
    right_hamiltonian_coordinates,right_density_coordinates]
  rw [diagonal_probability _ _
    (by simpa [RightMixed.chain_zero] using RightMixed.chain_nonzero 0)
    RightMixed.chain RightMixed.polynomial (fun _ => rfl)
    (by simpa [RightMixed.polynomial,ThreeAtomOperator.polynomial] using
      CertifiedPolynomialDegrees.three (225/169))
    (by intro i j hij; simp [RightMixed.gram,hij])]
  exact RightMixed.exact_probabilities i

theorem right_purified (i : Fin 5) :
    degreeProbability PurifiedCovariance.originalGenerator PurifiedCovariance.originalSeed
      i.val (Real.pi/3) = Spectral.RightPurified.probabilities i := by
  have hH : PurifiedCovariance.originalGenerator.IsHermitian := by
    change (PurifiedCovariance.lift (States.hR.map Complex.ofReal))ᴴ = _
    rw [PurifiedCovariance.lift_adjoint,right_hermitian.eq]
    rfl
  rw [← degreeProbability_changeBasis PurifiedCovariance.basis _ _
    PurifiedCovariance.basis_unitary PurifiedCovariance.basis_unitary_reverse hH,
    PurifiedCovariance.generator_coordinates,PurifiedCovariance.seed_coordinates]
  rw [diagonal_probability _ _
    (by intro hz; have h := PurifiedChain.seed_norm; simp [hz,hsInner] at h)
    PurifiedChain.chain PurifiedChain.polynomial (fun _ => rfl) right_purified_degree
    (by intro i j hij; simp [PurifiedChain.gram,hij])]
  change PurifiedChain.chainProbability i (Real.pi/3) = _
  rw [PurifiedChain.probability_eq_spectral,Spectral.RightPurified.time_probabilities]

end
end Krylov.WitnessProbabilityAPI
