import Krylov.CertifiedFamilyGS
import Krylov.GSUnitaryTransport
import Krylov.RightIntervalBound

namespace Krylov.WitnessSourceAPI
open Matrix OperatorBridge ConcreteChains UnitaryCovariance
open PhysicalCurvatureNecessary MatrixGSBridge
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 2000000

lemma complex_trace_one {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (h : trace A=1) : trace (A.map Complex.ofReal)=1 := by
  simpa [Matrix.trace] using congrArg Complex.ofReal h

lemma left_hamiltonian : States.hL.map Complex.ofReal = hamiltonian States.energyL := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [States.hL,States.energyL,hamiltonian,Matrix.diagonal]

lemma right_hermitian : (States.hR.map Complex.ofReal).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [States.hR,Matrix.conjTranspose_apply]

lemma left_mixed_chain (t : ℝ) :
    PerturbedDynamics.actualComplexity
      (PerturbedDynamics.liouvillian (hamiltonian States.energyL))
      (normalizedSeed LeftMixed.seed) t =
      chainComplexity States.energyL LeftMixed.seed LeftMixed.chain t := by
  apply CertifiedFamilyGS.actual_eq_chainComplexity _ _
    (by simpa [LeftMixed.chain_zero] using LeftMixed.chain_nonzero 0)
    _ LeftMixed.polynomial
  · intro i; rfl
  · simpa [LeftMixed.polynomial,ThreeAtomOperator.polynomial] using
      CertifiedPolynomialDegrees.three (3/182) 
  · intro i j hij; simp [LeftMixed.gram,hij]
  · exact LeftMixed.chain_spans_cyclic

lemma left_spread_chain (t : ℝ) :
    PerturbedDynamics.actualComplexity
      (PerturbedDynamics.liouvillian (hamiltonian States.energyL))
      (normalizedSeed LeftSpread.seed) t =
      chainComplexity States.energyL LeftSpread.seed LeftSpread.chain t := by
  apply CertifiedFamilyGS.actual_eq_chainComplexity _ _
    (by simpa [LeftSpread.chain_zero] using LeftSpread.chain_nonzero 0)
    _ LeftSpread.polynomial
  · intro i; rfl
  · simpa [LeftSpread.polynomial,ThreeAtomOperator.polynomial] using
      CertifiedPolynomialDegrees.three (1/42)
  · intro i j hij; simp [LeftSpread.gram,hij]
  · exact LeftSpread.chain_spans_cyclic

theorem left_mixed_eq (t : ℝ) :
    mixedComplexity (States.hL.map Complex.ofReal) (States.rhoL.map Complex.ofReal) t =
      chainComplexity States.energyL LeftMixed.seed LeftMixed.chain t := by
  rw [mixedComplexity,left_hamiltonian]
  exact left_mixed_chain t

theorem left_spread_eq (t : ℝ) :
    PurificationBranches.spread
      (PurificationBranches.generatorU (States.hL.map Complex.ofReal))
      (PurificationBranches.seed complex_rhoL_posDef.posSemidef) t =
      chainComplexity States.energyL LeftSpread.seed LeftSpread.chain t := by
  rw [spread_eq_normalized (by rw [left_hamiltonian]; exact diagonal_hermitian _)
    _ (complex_trace_one _ States.rhoL_trace),← complex_rootL_canonical,left_hamiltonian]
  exact left_spread_chain t

theorem prop_left :
    PurificationBranches.spread
      (PurificationBranches.generatorU (States.hL.map Complex.ofReal))
      (PurificationBranches.seed complex_rhoL_posDef.posSemidef) Real.pi = 82/441 ∧
    mixedComplexity (States.hL.map Complex.ofReal) (States.rhoL.map Complex.ofReal) Real.pi =
      1074/8281 ∧
    PurificationBranches.spread
      (PurificationBranches.generatorU (States.hL.map Complex.ofReal))
      (PurificationBranches.seed complex_rhoL_posDef.posSemidef) Real.pi -
      mixedComplexity (States.hL.map Complex.ofReal) (States.rhoL.map Complex.ofReal) Real.pi =
      4192/74529 := by
  rw [left_spread_eq,left_mixed_eq,LeftSpread.exact_complexity,LeftMixed.exact_complexity]
  norm_num

lemma right_mixed_chain (t : ℝ) :
    PerturbedDynamics.actualComplexity
      (PerturbedDynamics.liouvillian (hamiltonian States.energyR))
      (normalizedSeed RightMixed.seed) t =
      chainComplexity States.energyR RightMixed.seed RightMixed.chain t := by
  apply CertifiedFamilyGS.actual_eq_chainComplexity _ _
    (by simpa [RightMixed.chain_zero] using RightMixed.chain_nonzero 0)
    _ RightMixed.polynomial
  · intro i; rfl
  · simpa [RightMixed.polynomial,ThreeAtomOperator.polynomial] using
      CertifiedPolynomialDegrees.three (225/169)
  · intro i j hij; simp [RightMixed.gram,hij]
  · exact RightMixed.chain_spans_cyclic

lemma right_purified_degree (i : Fin 5) :
    (PurifiedChain.polynomial i).degree=(i.val : WithBot ℕ) := by
  fin_cases i
  · simp [PurifiedChain.polynomial]
  · simp [PurifiedChain.polynomial]
  · exact Polynomial.degree_X_pow_sub_C (by norm_num : 0 < (2:ℕ)) (17/13 : ℂ)
  · simpa using CertifiedPolynomialDegrees.leading_cubic (1:ℂ) (77/26) (by norm_num)
  · simpa using CertifiedPolynomialDegrees.leading_quartic (1:ℂ) (60944/14534)
      (23409/14534) (by norm_num)

lemma right_purified_chain (t : ℝ) :
    PerturbedDynamics.actualComplexity
      (PerturbedDynamics.liouvillian (hamiltonian PurifiedChain.energies))
      (normalizedSeed PurifiedChain.seed) t = PurifiedChain.complexity t := by
  apply CertifiedFamilyGS.actual_eq_chainComplexity _ _
    (by intro hz; have h := PurifiedChain.seed_norm; simp [hz,hsInner] at h)
    _ PurifiedChain.polynomial
  · intro i; rfl
  · exact right_purified_degree
  · intro i j hij; simp [PurifiedChain.gram,hij]
  · exact PurifiedChain.chain_spans_cyclic

theorem right_mixed_eq (t : ℝ) :
    mixedComplexity (States.hR.map Complex.ofReal) (States.rhoR.map Complex.ofReal) t =
      ∑ i : Fin 3, (i.val : ℝ)*matrixProbability (States.hR.map Complex.ofReal)
        (States.rhoR.map Complex.ofReal) (rightOriginalChain i) t := by
  unfold mixedComplexity
  rw [← GSUnitaryTransport.actual_changeBasis rightBasis _ _ rightBasis_unitary
    rightBasis_unitary_reverse right_hermitian,
    right_hamiltonian_coordinates,right_density_coordinates,right_mixed_chain]
  simp [chainComplexity,right_original_probability]

theorem right_purified_eq (t : ℝ) :
    PurificationBranches.pureOperator
      (PurificationBranches.generatorI (States.hR.map Complex.ofReal))
      (PurificationBranches.seed complex_rhoR_posDef.posSemidef) t =
      ∑ i : Fin 5, (i.val : ℝ)*matrixProbability PurifiedCovariance.originalGenerator
        PurifiedCovariance.originalSeed (PurifiedCovariance.originalChain i) t := by
  rw [pure_eq_normalized right_hermitian _ (complex_trace_one _ States.rhoR_trace),
    ← complex_rootR_canonical,PurificationBranches.generatorI_eq_kronecker]
  change PerturbedDynamics.actualComplexity
    (PerturbedDynamics.liouvillian PurifiedCovariance.originalGenerator)
    (normalizedSeed PurifiedCovariance.originalSeed) t = _
  have hH : PurifiedCovariance.originalGenerator.IsHermitian := by
    change (PurifiedCovariance.lift (States.hR.map Complex.ofReal))ᴴ = _
    rw [PurifiedCovariance.lift_adjoint,right_hermitian.eq]
    rfl
  rw [← GSUnitaryTransport.actual_changeBasis PurifiedCovariance.basis _ _
    PurifiedCovariance.basis_unitary PurifiedCovariance.basis_unitary_reverse hH,
    PurifiedCovariance.generator_coordinates,PurifiedCovariance.seed_coordinates,
    right_purified_chain]
  simp [PurifiedChain.complexity,PurifiedCovariance.original_probability]

theorem prop_right :
    mixedComplexity (States.hR.map Complex.ofReal) (States.rhoR.map Complex.ofReal)
      (Real.pi/3) = 1141425/913952 ∧
    PurificationBranches.pureOperator
      (PurificationBranches.generatorI (States.hR.map Complex.ofReal))
      (PurificationBranches.seed complex_rhoR_posDef.posSemidef) (Real.pi/3) =
      2967537/2456246 ∧
    mixedComplexity (States.hR.map Complex.ofReal) (States.rhoR.map Complex.ofReal)
      (Real.pi/3) - PurificationBranches.pureOperator
        (PurificationBranches.generatorI (States.hR.map Complex.ofReal))
        (PurificationBranches.seed complex_rhoR_posDef.posSemidef) (Real.pi/3) =
      1600683/39299936 := by
  rw [right_mixed_eq,right_purified_eq,right_original_complexity,
    PurifiedCovariance.original_complexity]
  norm_num

theorem right_interval {t : ℝ} (ht : 0<t) (hu : t<1/2704) :
    (4/169)*t^2-64*t^3 ≤
      mixedComplexity (States.hR.map Complex.ofReal) (States.rhoR.map Complex.ofReal) t -
      PurificationBranches.pureOperator
        (PurificationBranches.generatorI (States.hR.map Complex.ofReal))
        (PurificationBranches.seed complex_rhoR_posDef.posSemidef) t ∧
      0<(4/169)*t^2-64*t^3 := by
  rw [right_mixed_eq,right_purified_eq]
  exact RightIntervalBound.original_lower_bound ht hu

end
end Krylov.WitnessSourceAPI
