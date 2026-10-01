import Mathlib

/-! The scalar final step of the explicit Taylor certificates. The norm and
Taylor estimates supplying the lower-bound hypotheses remain separate. -/
namespace Krylov.ShortTime

theorem right_quadratic_gap : (225:ℚ)/169 - 221/169 = 4/169 := by norm_num

theorem right_interval_polynomial {t : ℝ} (ht : 0 < t) (hub : t < 1/2704) :
    0 < (4/169:ℝ)*t^2 - 64*t^3 := by
  have h : 0 < (4/169:ℝ) - 64*t := by linarith
  have hp := mul_pos (sq_pos_of_pos ht) h
  nlinarith

theorem right_interval_of_remainder {C K t : ℝ} (ht : 0 < t) (hub : t < 1/2704)
    (hbound : (4/169:ℝ)*t^2 - 64*t^3 ≤ C-K) : K < C := by
  have hp := right_interval_polynomial ht hub
  linarith

theorem perturbed_quadratic_gap {δ : ℝ} (hδ : δ^2 < 1/135) :
    0 < (4-540*δ^2)/169 := by linarith

theorem perturbed_finite_polynomial :
    (53/3380:ℚ)*(1/20000)^2 - (21296/125)*(1/20000)^3 =
    378247/21125000000000000 := by norm_num

theorem perturbed_finite_of_remainder {C K : ℝ}
    (hbound : (53/3380:ℝ)*(1/20000)^2 - (21296/125)*(1/20000)^3 ≤ C-K) :
    (378247/21125000000000000:ℝ) ≤ C-K ∧ K < C := by
  norm_num at hbound
  constructor
  · exact hbound
  · linarith
end Krylov.ShortTime
