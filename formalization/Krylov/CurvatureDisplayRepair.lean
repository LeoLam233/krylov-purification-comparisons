import Krylov.CubicRemainder
import Krylov.PhysicalCurvatureNecessary

namespace Krylov.CurvatureDisplayRepair
open Matrix PerturbedDynamics TaylorRemainder
open scoped InnerProductSpace Topology ComplexOrder
noncomputable section
set_option maxHeartbeats 2000000

/-- The quartic Taylor estimate holds on both sides of zero. -/
theorem quartic_remainder_alltime {f : ℝ → ℝ} {k B : ℝ} (t : ℝ)
    (hf : ContDiff ℝ 4 f) (h0 : f 0=0) (h1 : deriv f 0=0)
    (h2 : iteratedDeriv 2 f 0=2*k) (h3 : iteratedDeriv 3 f 0=0)
    (hB : ∀ x,|iteratedDeriv 4 f x|≤B) :
    |f t-k*t^2| ≤ B*t^4/24 := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · let g : ℝ → ℝ := fun x => f (-x)
    have hg : ContDiff ℝ 4 g := hf.comp contDiff_id.neg
    have hg0 : g 0=0 := by simpa [g] using h0
    have hg1 : deriv g 0=0 := by simp [g,deriv_comp_neg,h1]
    have hg2 : iteratedDeriv 2 g 0=2*k := by
      simpa [g,iteratedDeriv_comp_neg] using h2
    have hg3 : iteratedDeriv 3 g 0=0 := by
      simp [g,iteratedDeriv_comp_neg,h3]
    have hgB : ∀ x,|iteratedDeriv 4 g x|≤B := by
      intro x
      simpa [g,iteratedDeriv_comp_neg,show (-1 : ℝ)^4=1 by norm_num] using hB (-x)
    have h := quartic_remainder (t := -t) (by linarith) hg hg0 hg1 hg2 hg3
      (fun x _ => hgB x)
    simpa [g,show (-t)^4=t^4 by ring] using h
  · subst t; simp [h0]
  · exact quartic_remainder ht hf h0 h1 h2 h3 (fun x _ => hB x)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem actual_quartic_remainder_alltime (L : E →L[ℂ] E) (hL : IsSelfAdjoint L)
    (v : E) (hv : ‖v‖=1) (hov : ⟪v,L v⟫_ℂ=0) (t : ℝ) :
    |actualComplexity L v t-‖L v‖^2*t^2| ≤
      ((2*‖L‖)^4*‖numberOperator (powerSequence L v)‖)*t^4/24 := by
  obtain ⟨h0,h1,h2⟩ := actual_initial_data L v hov
  apply quartic_remainder_alltime t (actualComplexity_contDiff L v 4) h0 h1 h2
    (actual_third_zero L hL v hov)
  intro x
  rw [actualComplexity_eq_expectation]
  have h := abs_iteratedDeriv_le (skewGenerator L)
    (numberOperator (powerSequence L v)) v 4 x (by rw [evolution_norm L hL,hv])
  simpa [skewGenerator,norm_smul] using h

theorem right_mixed_coefficient : Perturbation.mixedCurvature 0 = 225/169 := by
  have hr : States.rhoR = !![8/13,0,0;0,1/26,0;0,0,9/26] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [States.rhoR, Matrix.diagonal]
  norm_num [Perturbation.mixedCurvature, States.hsNormSq, Matrix.trace,
    Matrix.mul_apply, hr, Perturbation.hamiltonian, Fin.sum_univ_succ]

theorem right_purified_coefficient : Perturbation.purifiedCurvature 0 = 221/169 := by
  have hr : States.rhoR = !![8/13,0,0;0,1/26,0;0,0,9/26] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [States.rhoR, Matrix.diagonal]
  norm_num [Perturbation.purifiedCurvature, Matrix.trace, Matrix.mul_apply,
    hr, Perturbation.hamiltonian, Fin.sum_univ_succ]

theorem right_mixed_remainder (t : ℝ) :
    |PerturbedDynamics.mixedComplexity 0 t-(225/169)*t^2| ≤
      ((2*‖liouvillian (complexHamiltonian 0)‖)^4*
        ‖numberOperator (powerSequence (liouvillian (complexHamiltonian 0)) mixedVector)‖)*t^4/24 := by
  simpa only [PerturbedDynamics.mixedComplexity,mixed_curvature,right_mixed_coefficient]
    using actual_quartic_remainder_alltime _
      (liouvillian_selfAdjoint _ (complexHamiltonian_hermitian 0))
      mixedVector mixedVector_unit (mixedVector_orthogonal 0) t

theorem right_purified_remainder (t : ℝ) :
    |PerturbedDynamics.purifiedComplexity 0 t-(221/169)*t^2| ≤
      ((2*‖liouvillian (purifiedGenerator 0)‖)^4*
        ‖numberOperator (powerSequence (liouvillian (purifiedGenerator 0)) purifiedVector)‖)*t^4/24 := by
  simpa only [PerturbedDynamics.purifiedComplexity,purified_curvature,right_purified_coefficient]
    using actual_quartic_remainder_alltime _
      (liouvillian_selfAdjoint _ (purifiedGenerator_hermitian 0))
      purifiedVector purifiedVector_unit (purifiedVector_orthogonal 0) t

theorem left_root_curvature :
    PhysicalCurvatureNecessary.hsNormSq
      ((States.hL.map Complex.ofReal)*UnitaryCovariance.complex_rhoL_posDef.posSemidef.sqrt -
        UnitaryCovariance.complex_rhoL_posDef.posSemidef.sqrt*(States.hL.map Complex.ofReal)) =
      1/42 := by
  rw [← UnitaryCovariance.complex_rootL_canonical]
  unfold PhysicalCurvatureNecessary.hsNormSq
  rw [rowVectorize_norm_sq]
  norm_num [States.hL,States.rootL,Matrix.mul_apply,Fin.sum_univ_succ,
    Matrix.diagonal,Complex.normSq_apply]
  simp only [Fin.ext_iff,Fin.val_ofNat',Fin.val_zero,Fin.val_one] 
  norm_num
  nlinarith [States.sL_sq]

theorem left_mixed_curvature :
    PhysicalCurvatureNecessary.hsNormSq
      ((States.hL.map Complex.ofReal)*(States.rhoL.map Complex.ofReal) -
        (States.rhoL.map Complex.ofReal)*(States.hL.map Complex.ofReal)) /
      PhysicalCurvatureNecessary.purity (States.rhoL.map Complex.ofReal) = 3/182 := by
  unfold PhysicalCurvatureNecessary.hsNormSq
  rw [rowVectorize_norm_sq]
  norm_num [PhysicalCurvatureNecessary.purity,States.hL,States.rhoL,
    Matrix.trace,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal,Complex.normSq_apply]
  simp only [Fin.ext_iff,Fin.val_ofNat',Fin.val_zero,Fin.val_one]
  norm_num

/-- The left counterexample violates the first necessary curvature inequality
for the actual canonical positive square root and the literal density. -/
theorem left_curvature_violation :
    PhysicalCurvatureNecessary.hsNormSq
      ((States.hL.map Complex.ofReal)*(States.rhoL.map Complex.ofReal) -
        (States.rhoL.map Complex.ofReal)*(States.hL.map Complex.ofReal)) /
      PhysicalCurvatureNecessary.purity (States.rhoL.map Complex.ofReal) <
    PhysicalCurvatureNecessary.hsNormSq
      ((States.hL.map Complex.ofReal)*UnitaryCovariance.complex_rhoL_posDef.posSemidef.sqrt -
        UnitaryCovariance.complex_rhoL_posDef.posSemidef.sqrt*(States.hL.map Complex.ofReal)) := by
  rw [left_mixed_curvature,left_root_curvature]
  norm_num

end
end Krylov.CurvatureDisplayRepair
