import Mathlib

/-!
Temporal CV consequences with explicitly exposed analytic hypotheses.
The peak-window-to-second-moment step is an actual interval-integral theorem.
The source families' complete period mean evaluations are NOT assumed as
axioms: they are remaining hypotheses in the conditional applications below.
-/
namespace Krylov.Temporal
open MeasureTheory
noncomputable section

def periodMean (f : ℝ → ℝ) : ℝ := (∫ t in (0:ℝ)..2*Real.pi, f t) / (2*Real.pi)
def cvSquared (f : ℝ → ℝ) : ℝ := periodMean (fun t => f t ^ 2) / (periodMean f)^2 - 1

theorem peak_second_moment {f : ℝ → ℝ} (hf : Continuous f)
    {ε L : ℝ} (hε : 0 < ε) (hεπ : ε ≤ Real.pi) (hL : 0 ≤ L)
    (hpeak : ∀ t ∈ Set.Icc (Real.pi-ε) (Real.pi+ε), L ≤ f t) :
    ε * L^2 / Real.pi ≤ periodMean (fun t => f t^2) := by
  have hc : Continuous (fun t => f t^2) := hf.pow 2
  have hab : Real.pi-ε ≤ Real.pi+ε := by linarith
  have hlocal : (2*ε)*L^2 ≤ ∫ t in Real.pi-ε..Real.pi+ε, f t^2 := by
    have h := intervalIntegral.integral_mono_on hab
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => L^2) volume _ _)
      (hc.intervalIntegrable _ _) (fun t ht => by
        have hp := hpeak t ht
        nlinarith)
    simpa [intervalIntegral.integral_const, smul_eq_mul, two_mul] using h
  have hglobal := intervalIntegral.integral_mono_interval (μ := volume)
    (show (0:ℝ) ≤ Real.pi-ε by linarith) hab
    (show Real.pi+ε ≤ 2*Real.pi by linarith)
    (Filter.Eventually.of_forall (fun t => sq_nonneg (f t))) (hc.intervalIntegrable _ _)
  unfold periodMean
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)).2
  have hcancel : ε * L^2 / Real.pi * (2*Real.pi) = 2*ε*L^2 := by
    field_simp; ring
  rw [hcancel]
  exact hlocal.trans hglobal

theorem main_cv_of_moments {ε μ ν : ℝ} (hε : 0 < ε) (hμ : 0 < μ)
    (hmean : μ ≤ 8) (hsecond : (289:ℝ)/(2073600*Real.pi*ε) ≤ ν) :
    (289:ℝ)/(132710400*Real.pi*ε)-1 ≤ ν/μ^2-1 := by
  have hden : 0 < (2073600:ℝ)*Real.pi*ε := by positivity
  have hnu : 0 ≤ ν := le_trans (by positivity) hsecond
  have hsq : μ^2 ≤ 64 := by nlinarith
  have hratio : ν/64 ≤ ν/μ^2 :=
    div_le_div_of_nonneg_left hnu (sq_pos_of_pos hμ) hsq
  have hs : (289:ℝ)/(132710400*Real.pi*ε) ≤ ν/64 := by
    have hh := (div_le_iff₀ hden).1 hsecond
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 132710400*Real.pi*ε)).2
    nlinarith
  linarith

theorem reciprocal_cv_of_moments {ε μ ν : ℝ} (hε : 0 < ε) (hμ : 0 < μ)
    (hmean : μ ≤ 216*ε) (hsecond : ε/(36*Real.pi) ≤ ν) :
    (1:ℝ)/(1679616*Real.pi*ε)-1 ≤ ν/μ^2-1 := by
  have hden : 0 < (36:ℝ)*Real.pi := by positivity
  have hnu : 0 ≤ ν := le_trans (by positivity) hsecond
  have hsq : μ^2 ≤ (216*ε)^2 := by nlinarith
  have hratio : ν/(216*ε)^2 ≤ ν/μ^2 :=
    div_le_div_of_nonneg_left hnu (sq_pos_of_pos hμ) hsq
  have hs : (1:ℝ)/(1679616*Real.pi*ε) ≤ ν/(216*ε)^2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hh := (div_le_iff₀ hden).1 hsecond
    nlinarith [mul_nonneg (show 0 ≤ ε by positivity) (sub_nonneg.mpr hh)]
  linarith

theorem main_finite_threshold : (80:ℝ)^2 <
    289/(132710400*Real.pi*(1/10000000000))-1 := by
  have hp := Real.pi_lt_d2
  have hpi := Real.pi_pos
  have h : (6401:ℝ) < 289/(132710400*Real.pi*(1/10000000000)) := by
    apply (lt_div_iff₀ (by positivity)).2
    nlinarith
  linarith


theorem reciprocal_finite_threshold : (40:ℝ)^2 <
    1/(1679616*Real.pi*(1/10000000000))-1 := by
  have hp := Real.pi_lt_d2
  have hpi := Real.pi_pos
  have h : (1601:ℝ) < 1/(1679616*Real.pi*(1/10000000000)) := by
    apply (lt_div_iff₀ (by positivity)).2
    nlinarith
  linarith

theorem cvSquared_scale (f : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0) :
    cvSquared (fun t => a*f t) = cvSquared f := by
  unfold cvSquared periodMean
  simp only [mul_pow, intervalIntegral.integral_const_mul]
  by_cases hm : (∫ t in (0:ℝ)..2*Real.pi, f t) = 0
  · simp [hm]
  · field_simp [ha, hm]
    ring

/-- The second-moment bound is obtained by integrating an actual peak, not
by assuming the source's displayed second-moment value. -/
theorem main_second_moment {f : ℝ → ℝ} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) (he : ε ≤ Real.pi)
    (hpeak : ∀ t ∈ Set.Icc (Real.pi-ε) (Real.pi+ε), 17/(1440*ε) ≤ f t) :
    289/(2073600*Real.pi*ε) ≤ periodMean (fun t => f t^2) := by
  have h := peak_second_moment hf hε he (by positivity) hpeak
  convert h using 1
  field_simp
  ring

theorem reciprocal_second_moment {f : ℝ → ℝ} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) (he : ε ≤ Real.pi)
    (hpeak : ∀ t ∈ Set.Icc (Real.pi-ε) (Real.pi+ε), 1/6 ≤ f t) :
    ε/(36*Real.pi) ≤ periodMean (fun t => f t^2) := by
  have h := peak_second_moment hf hε he (by norm_num : (0:ℝ) ≤ 1/6) hpeak
  convert h using 1
  ring

theorem main_cv_of_peak_and_mean {f : ℝ → ℝ} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) (he : ε ≤ Real.pi)
    (hmeanPos : 0 < periodMean f) (hmean : periodMean f ≤ 8)
    (hpeak : ∀ t ∈ Set.Icc (Real.pi-ε) (Real.pi+ε), 17/(1440*ε) ≤ f t) :
    289/(132710400*Real.pi*ε)-1 ≤ cvSquared f :=
  main_cv_of_moments hε hmeanPos hmean (main_second_moment hf hε he hpeak)

theorem reciprocal_cv_of_peak_and_mean {f : ℝ → ℝ} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) (he : ε ≤ Real.pi)
    (hmeanPos : 0 < periodMean f) (hmean : periodMean f ≤ 216*ε)
    (hpeak : ∀ t ∈ Set.Icc (Real.pi-ε) (Real.pi+ε), 1/6 ≤ f t) :
    1/(1679616*Real.pi*ε)-1 ≤ cvSquared f :=
  reciprocal_cv_of_moments hε hmeanPos hmean (reciprocal_second_moment hf hε he hpeak)


def cv (f : ℝ → ℝ) : ℝ := Real.sqrt (cvSquared f)

theorem cv_scale (f : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0) :
    cv (fun t => a*f t) = cv f := by
  rw [cv, cvSquared_scale f ha]; rfl

theorem main_finite_cv {f : ℝ → ℝ}
    (h : 289/(132710400*Real.pi*(1/10000000000))-1 ≤ cvSquared f) :
    80 < cv f :=
  Real.lt_sqrt_of_sq_lt (main_finite_threshold.trans_le h)

theorem reciprocal_finite_cv {f : ℝ → ℝ}
    (h : 1/(1679616*Real.pi*(1/10000000000))-1 ≤ cvSquared f) :
    40 < cv f :=
  Real.lt_sqrt_of_sq_lt (reciprocal_finite_threshold.trans_le h)

end
end Krylov.Temporal
