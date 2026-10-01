import Krylov.RightInterval
import Krylov.ShortTime

/-! The exact quantitative lower bound printed in source eq:right-interval. -/
namespace Krylov.RightIntervalBound
open RightInterval
open scoped BigOperators
noncomputable section

lemma polynomial_linear_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1/4) :
    (8/169)*x ≤ gapPolynomial x := by
  have hcoef : 0 ≤ (24317:ℝ)/28561-(50850:ℝ)/28561*x := by linarith
  have hquad := mul_nonneg (sq_nonneg x) hcoef
  have hquart : 0 ≤ (1051659:ℝ)/2456246*x^4 := by positivity
  unfold gapPolynomial
  nlinarith

lemma spectral_lower {t : ℝ} (ht : 0<t) (hu : t<1/2704) :
    (4/169)*t^2-64*t^3 ≤
      Spectral.timeComplexity Spectral.RightMixed.nodes Spectral.RightMixed.weights
        Spectral.RightMixed.polys t -
      Spectral.timeComplexity Spectral.RightPurified.nodes Spectral.RightPurified.weights
        Spectral.RightPurified.polys t := by
  obtain ⟨h0,h1⟩ := short_time_cos_range ht hu
  have hp := polynomial_linear_lower h0.le h1
  have hc := (abs_le.mp (Real.cos_bound (x := t) (by rw [abs_of_pos ht]; linarith))).2
  rw [abs_of_pos ht] at hc
  have hsmall : t≤1 := by linarith
  have hpow : t^4≤t^3 := by nlinarith [mul_nonneg (pow_nonneg ht.le 3) (sub_nonneg.mpr hsmall)]
  have ht3 : 0≤t^3 := by positivity
  rw [spectral_gap_polynomial]
  nlinarith

/-- The original-basis physical complexities satisfy the printed quantitative
bound on the entire stated interval, together with strict positivity. -/
theorem original_lower_bound {t : ℝ} (ht : 0<t) (hu : t<1/2704) :
    (4/169)*t^2-64*t^3 ≤
      (∑ k : Fin 3, (k.val : ℝ) * UnitaryCovariance.matrixProbability
        (States.hR.map Complex.ofReal) (States.rhoR.map Complex.ofReal)
        (UnitaryCovariance.rightOriginalChain k) t) -
      (∑ k : Fin 5, (k.val : ℝ) * UnitaryCovariance.matrixProbability
        PurifiedCovariance.originalGenerator PurifiedCovariance.originalSeed
        (PurifiedCovariance.originalChain k) t) ∧
      0 < (4/169)*t^2-64*t^3 := by
  constructor
  · simp_rw [PurifiedCovariance.original_probability,UnitaryCovariance.right_original_probability,
      PurifiedChain.probability_eq_spectral,ConcreteChains.RightMixed.probability_eq_spectral]
    exact spectral_lower ht hu
  · exact ShortTime.right_interval_polynomial ht hu
end
end Krylov.RightIntervalBound
