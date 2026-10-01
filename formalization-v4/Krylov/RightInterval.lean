import Krylov.PurifiedCovariance

/-! A direct exact trigonometric-polynomial proof of the right witness's
short-time interval. It avoids assuming the source's Taylor remainder estimate. -/
namespace Krylov.RightInterval
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def gapPolynomial (x : ℝ) : ℝ :=
  1051659/2456246*x^4 - 50850/28561*x^3 + 24317/28561*x^2 + 8/169*x

theorem spectral_gap_polynomial (t : ℝ) :
    Spectral.timeComplexity Spectral.RightMixed.nodes Spectral.RightMixed.weights
      Spectral.RightMixed.polys t -
    Spectral.timeComplexity Spectral.RightPurified.nodes Spectral.RightPurified.weights
      Spectral.RightPurified.polys t = gapPolynomial (1-Real.cos t) := by
  have hs : Real.sin t^2 = 1-Real.cos t^2 := by nlinarith [Real.sin_sq_add_cos_sq t]
  norm_num [Spectral.timeComplexity, Spectral.timeProbability, Spectral.realDot, Spectral.dot,
    Spectral.RightMixed.nodes, Spectral.RightMixed.weights, Spectral.RightMixed.polys,
    Spectral.RightPurified.nodes, Spectral.RightPurified.weights, Spectral.RightPurified.polys,
    Fin.sum_univ_succ, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul,
    show (-2:ℝ)*t = -(2*t) by ring]
  unfold gapPolynomial
  ring_nf
  rw [hs]
  ring

theorem gapPolynomial_positive {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1/4) :
    0 < gapPolynomial x := by
  have hcoef : 0 < (24317:ℝ)/28561 - (50850:ℝ)/28561*x := by linarith
  have hquad := mul_pos (sq_pos_of_pos hx) hcoef
  have hquart : 0 ≤ (1051659:ℝ)/2456246*x^4 := by positivity
  unfold gapPolynomial
  nlinarith

theorem short_time_cos_range {t : ℝ} (ht : 0 < t) (hu : t < 1/2704) :
    0 < 1-Real.cos t ∧ 1-Real.cos t ≤ 1/4 := by
  have hp := Real.pi_gt_three
  have hc : Real.cos t < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := t)
      (by norm_num) (by linarith) ht
    simpa using h
  have hb := Real.one_sub_sq_div_two_le_cos (x := t)
  constructor
  · linarith
  · have hs : t^2 < (1/2704:ℝ)^2 := by nlinarith
    nlinarith

theorem spectral_short_time_violation {t : ℝ} (ht : 0 < t) (hu : t < 1/2704) :
    Spectral.timeComplexity Spectral.RightPurified.nodes Spectral.RightPurified.weights
      Spectral.RightPurified.polys t <
    Spectral.timeComplexity Spectral.RightMixed.nodes Spectral.RightMixed.weights
      Spectral.RightMixed.polys t := by
  obtain ⟨h0,h1⟩ := short_time_cos_range ht hu
  have h := gapPolynomial_positive h0 h1
  rw [← spectral_gap_polynomial] at h
  linarith

theorem original_short_time_violation {t : ℝ} (ht : 0 < t) (hu : t < 1/2704) :
    (∑ k : Fin 5, (k.val : ℝ) * UnitaryCovariance.matrixProbability
      PurifiedCovariance.originalGenerator PurifiedCovariance.originalSeed
      (PurifiedCovariance.originalChain k) t) <
    (∑ k : Fin 3, (k.val : ℝ) * UnitaryCovariance.matrixProbability
      (States.hR.map Complex.ofReal) (States.rhoR.map Complex.ofReal)
      (UnitaryCovariance.rightOriginalChain k) t) := by
  simp_rw [PurifiedCovariance.original_probability, UnitaryCovariance.right_original_probability,
    PurifiedChain.probability_eq_spectral, ConcreteChains.RightMixed.probability_eq_spectral]
  exact spectral_short_time_violation ht hu

end
end Krylov.RightInterval
