import Krylov.PerturbedDynamics

namespace Krylov.CurvatureNecessary
open PerturbedDynamics TaylorRemainder
open scoped InnerProductSpace
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- An all-time complexity comparison forces the corresponding quadratic
curvature order; every regularity/remainder premise is derived from the genuine
finite-dimensional normalized-GS dynamics. -/
theorem curvature_le_of_all_time_le
    (L : E →L[ℂ] E) (M : F →L[ℂ] F) (hL : IsSelfAdjoint L) (hM : IsSelfAdjoint M)
    (v : E) (w : F) (hv : ‖v‖=1) (hw : ‖w‖=1)
    (hov : ⟪v,L v⟫_ℂ=0) (how : ⟪w,M w⟫_ℂ=0)
    (hcomp : ∀ t : ℝ, actualComplexity L v t ≤ actualComplexity M w t) :
    ‖L v‖^2 ≤ ‖M w‖^2 := by
  by_contra h
  have hk : 0 < ‖L v‖^2 - ‖M w‖^2 := sub_pos.mpr (lt_of_not_ge h)
  let B : ℝ := (2*‖L‖)^4*‖numberOperator (powerSequence L v)‖/24
  let D : ℝ := (2*‖M‖)^4*‖numberOperator (powerSequence M w)‖/24
  have hB : 0 ≤ B+D := by dsimp [B,D]; positivity
  obtain ⟨ε,hε,hpoly⟩ := positive_quadratic_minus_quartic hk hB
  have ht : 0 < ε/2 := by positivity
  have he : ε/2 < ε := by linarith
  have hp := hpoly (ε/2) ht he
  have hl := actual_quartic_remainder L hL v hv hov ht
  have hm := actual_quartic_remainder M hM w hw how ht
  have hl' : |actualComplexity L v (ε/2)-‖L v‖^2*(ε/2)^2| ≤ B*(ε/2)^4 := by
    simpa only [B,div_mul_eq_mul_div] using hl
  have hm' : |actualComplexity M w (ε/2)-‖M w‖^2*(ε/2)^2| ≤ D*(ε/2)^4 := by
    simpa only [D,div_mul_eq_mul_div] using hm
  have hlow := (abs_le.mp hl').1
  have hupp := (abs_le.mp hm').2
  have hc := hcomp (ε/2)
  nlinarith
end
end Krylov.CurvatureNecessary
