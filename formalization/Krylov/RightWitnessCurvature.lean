import Krylov.CurvatureDisplayRepair
import Krylov.WitnessSourceAPI

namespace Krylov.RightWitnessCurvature
open Matrix PerturbedDynamics PhysicalCurvatureNecessary WitnessSourceAPI
open scoped BigOperators InnerProductSpace ComplexOrder Topology Asymptotics
noncomputable section
set_option maxHeartbeats 1000000

lemma hamiltonian_zero : complexHamiltonian 0 = States.hR.map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexHamiltonian,Perturbation.hamiltonian,States.hR]

lemma mixed_seed_normalized : normalizedSeed mixedSeed = mixedVector := by
  have hn : ‖FactorTwo.rowVectorize mixedSeed‖ = Real.sqrt (1/2) := by
    rw [← mixedSeed_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  have hi : ‖FactorTwo.rowVectorize mixedSeed‖⁻¹ = Real.sqrt 2 := by
    rw [hn,Real.sqrt_div (by norm_num),Real.sqrt_one,one_div,inv_inv]
  simp only [normalizedSeed,hi,mixedVector]

lemma mixed_source (t : ℝ) :
    PhysicalCurvatureNecessary.mixedComplexity (States.hR.map Complex.ofReal)
      (States.rhoR.map Complex.ofReal) t = PerturbedDynamics.mixedComplexity 0 t := by
  rw [PhysicalCurvatureNecessary.mixedComplexity,PerturbedDynamics.mixedComplexity,
    hamiltonian_zero]
  exact congrArg (fun v => actualComplexity (liouvillian (States.hR.map Complex.ofReal)) v t)
    mixed_seed_normalized

lemma purified_source (t : ℝ) :
    PurificationBranches.pureOperator
      (PurificationBranches.generatorI (States.hR.map Complex.ofReal))
      (PurificationBranches.seed UnitaryCovariance.complex_rhoR_posDef.posSemidef) t =
      PerturbedDynamics.purifiedComplexity 0 t := by
  rw [PurificationBranches.pureOperator,← PureShortTime.operatorComplexity_physical _
    (PurificationBranches.generatorI_hermitian right_hermitian)]
  have hs : FactorTwo.pureSeed
      (PurificationBranches.seed UnitaryCovariance.complex_rhoR_posDef.posSemidef) =
      PurifiedCovariance.originalSeed := by
    have he := UnitaryCovariance.complex_rootR_canonical
    ext ⟨i,j⟩ ⟨k,l⟩
    simp only [FactorTwo.pureSeed,FactorTwo.outer,PurificationBranches.seed,
      PurifiedCovariance.originalSeed,Purification.pureSeed,PurifiedCovariance.originalRoot,
      ← he]
  rw [hs,PurificationBranches.generatorI_eq_kronecker]
  simp only [PerturbedDynamics.purifiedComplexity,purifiedGenerator,hamiltonian_zero,
    purifiedVector,PurifiedCovariance.lift]

theorem literal_curvatures :
    PhysicalCurvatureNecessary.hsNormSq
      ((States.hR.map Complex.ofReal)*(States.rhoR.map Complex.ofReal)-
        (States.rhoR.map Complex.ofReal)*(States.hR.map Complex.ofReal)) /
      PhysicalCurvatureNecessary.purity (States.rhoR.map Complex.ofReal) = 225/169 ∧
    2*energyVariance (States.rhoR.map Complex.ofReal) (States.hR.map Complex.ofReal) = 221/169 := by
  constructor
  · unfold PhysicalCurvatureNecessary.hsNormSq
    rw [rowVectorize_norm_sq]
    norm_num [PhysicalCurvatureNecessary.purity,States.hR,States.rhoR,
      Matrix.trace,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal,Complex.normSq_apply]
    simp only [Fin.ext_iff,Fin.val_ofNat',Fin.val_zero,Fin.val_one]
    norm_num
  · norm_num [energyVariance,States.hR,States.rhoR,Matrix.trace,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]

theorem right_curvature_violation :
    2*energyVariance (States.rhoR.map Complex.ofReal) (States.hR.map Complex.ofReal) <
    PhysicalCurvatureNecessary.hsNormSq
      ((States.hR.map Complex.ofReal)*(States.rhoR.map Complex.ofReal)-
        (States.rhoR.map Complex.ofReal)*(States.hR.map Complex.ofReal)) /
      PhysicalCurvatureNecessary.purity (States.rhoR.map Complex.ofReal) := by
  rw [literal_curvatures.1,literal_curvatures.2]
  norm_num

/-- The displayed right-witness coefficients, including both sides of time
zero, in precisely the source-defined physical complexity API. -/
theorem source_expansions :
    (fun t : ℝ => PhysicalCurvatureNecessary.mixedComplexity
      (States.hR.map Complex.ofReal) (States.rhoR.map Complex.ofReal) t -
      (225/169)*t^2) =O[nhds 0] (fun t : ℝ => t^4) ∧
    (fun t : ℝ => PurificationBranches.pureOperator
      (PurificationBranches.generatorI (States.hR.map Complex.ofReal))
      (PurificationBranches.seed UnitaryCovariance.complex_rhoR_posDef.posSemidef) t -
      (221/169)*t^2) =O[nhds 0] (fun t : ℝ => t^4) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound
      (((2*‖liouvillian (complexHamiltonian 0)‖)^4*
        ‖numberOperator (powerSequence (liouvillian (complexHamiltonian 0)) mixedVector)‖)/24)
    apply Filter.Eventually.of_forall
    intro t
    rw [mixed_source]
    simpa only [Real.norm_eq_abs,abs_pow,show |t|^4=t^4 by rw [← abs_pow,abs_of_nonneg (by positivity)],
      div_mul_eq_mul_div] using CurvatureDisplayRepair.right_mixed_remainder t
  · apply Asymptotics.IsBigO.of_bound
      (((2*‖liouvillian (purifiedGenerator 0)‖)^4*
        ‖numberOperator (powerSequence (liouvillian (purifiedGenerator 0)) purifiedVector)‖)/24)
    apply Filter.Eventually.of_forall
    intro t
    rw [purified_source]
    simpa only [Real.norm_eq_abs,abs_pow,show |t|^4=t^4 by rw [← abs_pow,abs_of_nonneg (by positivity)],
      div_mul_eq_mul_div] using CurvatureDisplayRepair.right_purified_remainder t

end
end Krylov.RightWitnessCurvature
