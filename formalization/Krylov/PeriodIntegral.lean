import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Real MeasureTheory intervalIntegral

namespace Krylov

private theorem poisson_aux_denom_pos {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    0 < 1 + r * Real.cos t := by
  have h := mul_nonneg hr (show 0 ≤ 1 + Real.cos t by linarith [Real.neg_one_le_cos t])
  linarith

private theorem poisson_denom_pos {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    0 < 1 + 2 * r * Real.cos t + r ^ 2 := by
  have h := mul_nonneg hr (show 0 ≤ 1 + Real.cos t by linarith [Real.neg_one_le_cos t])
  have hs : 0 < (1-r)^2 := sq_pos_of_pos (by linarith)
  nlinarith

private theorem hasDerivAt_poisson_primitive {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => x - 2 * Real.arctan (r * Real.sin x / (1 + r * Real.cos x)))
      ((1 - r ^ 2) / (1 + 2 * r * Real.cos t + r ^ 2)) t := by
  have hd : 1 + r * Real.cos t ≠ 0 := (poisson_aux_denom_pos hr hr1 t).ne'
  have hD : 1 + 2 * r * Real.cos t + r ^ 2 ≠ 0 := (poisson_denom_pos hr hr1 t).ne'
  have hs : 1 + (r * Real.sin t / (1 + r * Real.cos t)) ^ 2 ≠ 0 := by positivity
  have htrig : (r * Real.cos t)^2 + (r * Real.sin t)^2 = r^2 := by
    nlinarith [congrArg (fun x : ℝ => r^2*x) (Real.sin_sq_add_cos_sq t)]
  have hnorm : (1 + r * Real.cos t)^2 + (r * Real.sin t)^2 =
      1 + 2 * r * Real.cos t + r^2 := by nlinarith [htrig]
  have hnum : r * Real.cos t * (1 + r * Real.cos t) + r * Real.sin t * (r * Real.sin t) =
      r * Real.cos t + r^2 := by nlinarith [htrig]
  convert (hasDerivAt_id t).sub
    ((((Real.hasDerivAt_sin t).const_mul r).div
      (((Real.hasDerivAt_cos t).const_mul r).const_add 1) hd).arctan.const_mul 2) using 1
  field_simp
  rw [hnorm, hnum]
  ring

/-- A real-variable evaluation of the Poisson-kernel period integral, derived from a
single globally smooth arctangent primitive. -/
theorem integral_poisson_kernel {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
      (1 - r ^ 2) / (1 + 2 * r * Real.cos t + r ^ 2)) = 2 * Real.pi := by
  have hc : Continuous (fun t : ℝ =>
      (1 - r ^ 2) / (1 + 2 * r * Real.cos t + r ^ 2)) := by
    exact continuous_const.div
      ((continuous_const.add (continuous_const.mul Real.continuous_cos)).add continuous_const)
      (fun t => (poisson_denom_pos hr hr1 t).ne')
  rw [integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_poisson_primitive hr hr1 t) (hc.intervalIntegrable _ _)]
  simp

/-- The full-period reciprocal quadratic-cosine integral for positive parameters. -/
theorem integral_inv_cos_half_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), 1 / (a * (Real.cos (t / 2))^2 + b)) =
      (2 * Real.pi) / Real.sqrt (b * (a+b)) := by
  let p := Real.sqrt (a+b)
  let q := Real.sqrt b
  have hp : 0 < p := Real.sqrt_pos.mpr (by linarith)
  have hq : 0 < q := Real.sqrt_pos.mpr hb
  have hp2 : p^2 = a+b := Real.sq_sqrt (by linarith)
  have hq2 : q^2 = b := Real.sq_sqrt hb.le
  have hqp : q < p := by nlinarith
  have hpq : 0 < p+q := by linarith
  let r := (p-q)/(p+q)
  have hr : 0 ≤ r := le_of_lt (div_pos (by linarith) hpq)
  have hr1 : r < 1 := (div_lt_one hpq).mpr (by linarith)
  have hpoint (t : ℝ) :
      (1-r^2)/(1+2*r*Real.cos t+r^2) = p*q * (1/(a*(Real.cos (t/2))^2+b)) := by
    have hc : Real.cos t = 2 * (Real.cos (t/2))^2 - 1 := by
      convert Real.cos_two_mul (t/2) using 1
      congr 1
      ring
    have hden : a * (Real.cos (t/2))^2 + b ≠ 0 := by positivity
    rw [mul_one_div, div_eq_div_iff (poisson_denom_pos hr hr1 t).ne' hden]
    dsimp [r]
    rw [hc]
    field_simp
    linear_combination
      -(4*p*q*(p+q)^3*(Real.cos (t/2))^2) * hp2 -
      (4*p*q*(p+q)^3*(1-(Real.cos (t/2))^2)) * hq2
  have hint := integral_poisson_kernel hr hr1
  have hrewrite :
      (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), (1-r^2)/(1+2*r*Real.cos t+r^2)) =
      p*q * (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), 1/(a*(Real.cos (t/2))^2+b)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro t _
    exact hpoint t
  rw [hrewrite] at hint
  have hroot : Real.sqrt (b*(a+b)) = p*q := by
    rw [Real.sqrt_mul hb.le]
    exact mul_comm _ _
  rw [hroot]
  exact (eq_div_iff (mul_ne_zero hp.ne' hq.ne')).mpr (by nlinarith [hint])

/-- The normalized period mean has a closed positive-parameter formula. -/
theorem mean_inv_cos_half_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (1/(2*Real.pi)) *
      (∫ t : ℝ in (0 : ℝ)..(2*Real.pi), 1/(a*(Real.cos (t/2))^2+b)) =
      1/Real.sqrt (b*(a+b)) := by
  rw [integral_inv_cos_half_sq ha hb]
  field_simp

/-- Period averaging respects arbitrary real affine changes of the reciprocal profile. -/
theorem mean_affine_inv_cos_half_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (A B C : ℝ) :
    (1 / (2 * Real.pi)) *
      (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
        A * (C + B / (a * (Real.cos (t / 2)) ^ 2 + b))) =
      A * (C + B / Real.sqrt (b * (a + b))) := by
  have hc : Continuous (fun t : ℝ => 1 / (a * (Real.cos (t / 2)) ^ 2 + b)) := by
    apply continuous_const.div
    · exact (continuous_const.mul
        ((Real.continuous_cos.comp (continuous_id.div_const 2)).pow 2)).add continuous_const
    · intro t
      positivity
  have hi : IntervalIntegrable
      (fun t : ℝ => 1 / (a * (Real.cos (t / 2)) ^ 2 + b)) volume 0 (2 * Real.pi) :=
    hc.intervalIntegrable _ _
  simp_rw [div_eq_mul_one_div B]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul B),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_inv_cos_half_sq ha hb]
  simp only [sub_zero, smul_eq_mul]
  field_simp
  ring

end Krylov
