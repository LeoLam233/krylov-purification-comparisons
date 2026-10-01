import Krylov.TemporalFamilies

/-!
# Measurable-ratio CV bounds

The temporal CV estimates do not need continuity of the ratio at common
recurrences. A measurable ratio and almost-everywhere comparison envelope
suffice; integrability of both first and second moments is proved from the
continuous envelope. Thus arbitrary changes on a null recurrence set are
allowed. Identification of a physical Krylov ratio still needs its own proof.
-/

noncomputable section
namespace Krylov.TemporalMeasure
open MeasureTheory
open Krylov.TemporalFamilies

/-- A measurable function bounded almost everywhere by a continuous envelope
has integrable first and second moments on every finite interval. -/
theorem envelope_integrable {f r : ℝ → ℝ} (hf : Continuous f) (hr : Measurable r)
    {B a b : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ᵐ t ∂volume, 0 ≤ r t ∧ r t ≤ B * f t) :
    IntervalIntegrable r volume a b ∧ IntervalIntegrable (fun t => r t ^ 2) volume a b := by
  have hc : Continuous (fun t => B * f t) := continuous_const.mul hf
  constructor
  · apply (hc.intervalIntegrable a b).mono_fun' hr.aestronglyMeasurable
    apply ae_restrict_of_ae
    filter_upwards [hbound] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  · apply ((hc.pow 2).intervalIntegrable a b).mono_fun' (hr.pow_const 2).aestronglyMeasurable
    apply ae_restrict_of_ae
    filter_upwards [hbound] with t ht
    have hs : r t ^ 2 ≤ (B * f t) ^ 2 := by nlinarith [ht.1, ht.2]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (r t))] using hs

theorem periodMean_mono_ae {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi))
    (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (hfg : ∀ᵐ t ∂volume, f t ≤ g t) : Temporal.periodMean f ≤ Temporal.periodMean g := by
  unfold Temporal.periodMean
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact intervalIntegral.integral_mono_ae (by positivity) hf hg hfg

/-- Almost-everywhere peak bound gives the same actual second-moment estimate. -/
theorem peak_second_moment_ae {r : ℝ → ℝ}
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume 0 (2 * Real.pi))
    {ε L : ℝ} (he : 0 < ε) (heπ : ε ≤ Real.pi) (hL : 0 ≤ L)
    (hpeak : ∀ᵐ t ∂volume, t ∈ Set.Icc (Real.pi - ε) (Real.pi + ε) → L ≤ r t) :
    ε * L ^ 2 / Real.pi ≤ Temporal.periodMean (fun t => r t ^ 2) := by
  have hab : Real.pi - ε ≤ Real.pi + ε := by linarith
  have hlocalint : IntervalIntegrable (fun t => r t ^ 2) volume (Real.pi - ε) (Real.pi + ε) := by
    apply hr2.mono_set
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hlocal : (2 * ε) * L ^ 2 ≤ ∫ t in Real.pi - ε..Real.pi + ε, r t ^ 2 := by
    have h := intervalIntegral.integral_mono_ae_restrict hab
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => L ^ 2) volume _ _)
      hlocalint (by
        filter_upwards [ae_restrict_of_ae hpeak, ae_restrict_mem measurableSet_Icc] with t ht htmem
        have h := ht htmem
        nlinarith)
    simpa [intervalIntegral.integral_const, smul_eq_mul, two_mul] using h
  have hglobal := intervalIntegral.integral_mono_interval (μ := volume)
    (show (0 : ℝ) ≤ Real.pi - ε by linarith) hab
    (show Real.pi + ε ≤ 2 * Real.pi by linarith)
    (Filter.Eventually.of_forall (fun t => sq_nonneg (r t))) hr2
  unfold Temporal.periodMean
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).2
  have hcancel : ε * L ^ 2 / Real.pi * (2 * Real.pi) = 2 * ε * L ^ 2 := by
    field_simp
    ring
  rw [hcancel]
  exact hlocal.trans hglobal

/-- Main CV bound for measurable ratios with only a.e. envelope hypotheses. -/
theorem main_cv_of_measurable_envelope {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    {r : ℝ → ℝ} (hr : Measurable r)
    (hlower : ∀ᵐ t ∂volume, mainRatio ε (Real.cos (t / 2) ^ 2) / 8 ≤ r t)
    (hupper : ∀ᵐ t ∂volume, r t ≤ 8 * mainRatio ε (Real.cos (t / 2) ^ 2)) :
    289 / (132710400 * Real.pi * ε) - 1 ≤ Temporal.cvSquared r := by
  have hf := mainRatio_continuous he
  have hb : ∀ᵐ t ∂volume, 0 ≤ r t ∧ r t ≤ 8 * mainRatio ε (Real.cos (t / 2) ^ 2) := by
    filter_upwards [hlower, hupper] with t hl hu
    have hp := mainRatio_pos he he' (sq_nonneg (Real.cos (t / 2)))
    exact ⟨by linarith, hu⟩
  obtain ⟨hr1, hr2⟩ := envelope_integrable hf hr (by norm_num : (0 : ℝ) ≤ 8)
    (a := 0) (b := 2 * Real.pi) hb
  have hlow := periodMean_mono_ae ((continuous_const.mul hf).intervalIntegrable _ _) hr1
    (show ∀ᵐ t ∂volume, (1 / 8 : ℝ) * mainRatio ε (Real.cos (t / 2) ^ 2) ≤ r t by
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hlower)
  rw [periodMean_const_mul, main_periodMean_eq he he'] at hlow
  have hμ : 0 < Temporal.periodMean r :=
    lt_of_lt_of_le (mul_pos (by norm_num) (mainMeanFormula_pos he he')) hlow
  have hupp := periodMean_mono_ae hr1 ((continuous_const.mul hf).intervalIntegrable _ _) hupper
  rw [periodMean_const_mul, main_periodMean_eq he he'] at hupp
  have hμupper : Temporal.periodMean r ≤ 8 := by linarith [mainMeanFormula_bound he he']
  have hpeak : ∀ᵐ t ∂volume, t ∈ Set.Icc (Real.pi - ε) (Real.pi + ε) →
      17 / (1440 * ε) ≤ r t := by
    filter_upwards [hlower] with t hl
    intro ht
    have hp := div_le_div_of_nonneg_right (mainRatio_time_peak he he' ht)
      (by norm_num : (0 : ℝ) ≤ 8)
    have heq : (17 / (180 * ε)) / 8 = 17 / (1440 * ε) := by ring
    rw [heq] at hp
    exact hp.trans hl
  have hm := peak_second_moment_ae hr2 he (by linarith [Real.pi_gt_three])
    (by positivity : 0 ≤ 17 / (1440 * ε)) hpeak
  have hmoment : 289 / (2073600 * Real.pi * ε) ≤ Temporal.periodMean (fun t => r t ^ 2) := by
    convert hm using 1
    field_simp
    ring
  exact Temporal.main_cv_of_moments he hμ hμupper hmoment

/-- Reciprocal CV bound for measurable ratios with only a.e. envelopes. -/
theorem reciprocal_cv_of_measurable_envelope {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16)
    {q : ℝ → ℝ} (hq : Measurable q)
    (hlower : ∀ᵐ t ∂volume, reciprocalRatio ε (Real.cos (t / 2) ^ 2) / 8 ≤ q t)
    (hupper : ∀ᵐ t ∂volume, q t ≤ 8 * reciprocalRatio ε (Real.cos (t / 2) ^ 2)) :
    1 / (1679616 * Real.pi * ε) - 1 ≤ Temporal.cvSquared q := by
  have hf := reciprocalRatio_continuous he
  have hb : ∀ᵐ t ∂volume, 0 ≤ q t ∧ q t ≤ 8 * reciprocalRatio ε (Real.cos (t / 2) ^ 2) := by
    filter_upwards [hlower, hupper] with t hl hu
    have hp := reciprocalRatio_pos he (sq_nonneg (Real.cos (t / 2)))
    exact ⟨by linarith, hu⟩
  obtain ⟨hq1, hq2⟩ := envelope_integrable hf hq (by norm_num : (0 : ℝ) ≤ 8)
    (a := 0) (b := 2 * Real.pi) hb
  have hlow := periodMean_mono_ae ((continuous_const.mul hf).intervalIntegrable _ _) hq1
    (show ∀ᵐ t ∂volume, (1 / 8 : ℝ) * reciprocalRatio ε (Real.cos (t / 2) ^ 2) ≤ q t by
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hlower)
  rw [periodMean_const_mul, reciprocal_periodMean_eq he] at hlow
  have hμ : 0 < Temporal.periodMean q :=
    lt_of_lt_of_le (mul_pos (by norm_num) (reciprocalMeanFormula_pos he he')) hlow
  have hupp := periodMean_mono_ae hq1 ((continuous_const.mul hf).intervalIntegrable _ _) hupper
  rw [periodMean_const_mul, reciprocal_periodMean_eq he] at hupp
  have hμupper : Temporal.periodMean q ≤ 216 * ε := by linarith [reciprocalMeanFormula_bound he he']
  have hpeak : ∀ᵐ t ∂volume, t ∈ Set.Icc (Real.pi - ε) (Real.pi + ε) →
      1 / 6 ≤ q t := by
    filter_upwards [hlower] with t hl
    intro ht
    have hp := div_le_div_of_nonneg_right (reciprocalRatio_time_peak he he' ht)
      (by norm_num : (0 : ℝ) ≤ 8)
    norm_num at hp
    exact hp.trans hl
  have hm := peak_second_moment_ae hq2 he (by linarith [Real.pi_gt_three])
    (by norm_num : (0 : ℝ) ≤ 1 / 6) hpeak
  have hmoment : ε / (36 * Real.pi) ≤ Temporal.periodMean (fun t => q t ^ 2) := by
    convert hm using 1
    ring
  exact Temporal.reciprocal_cv_of_moments he hμ hμupper hmoment

/-- The CV-squared functional ignores changes on a null set. -/
theorem cvSquared_congr_ae {r s : ℝ → ℝ} (hrs : r =ᵐ[volume] s) :
    Temporal.cvSquared r = Temporal.cvSquared s := by
  have hmean : (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), r t) =
      ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), s t :=
    intervalIntegral.integral_congr_ae (hrs.mono (fun _ h _ => h))
  have hsquare : (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), r t ^ 2) =
      ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), s t ^ 2 :=
    intervalIntegral.integral_congr_ae (hrs.mono (fun _ h _ => by rw [h]))
  simp only [Temporal.cvSquared, Temporal.periodMean, hmean, hsquare]

/-- Any assignments at a countable recurrence set give the same CV-squared. -/
theorem cvSquared_congr_off_countable {r s : ℝ → ℝ} {N : Set ℝ}
    (hN : N.Countable) (hrs : ∀ t : ℝ, t ∉ N → r t = s t) :
    Temporal.cvSquared r = Temporal.cvSquared s := by
  apply cvSquared_congr_ae
  filter_upwards [hN.ae_not_mem volume] with t ht
  exact hrs t ht

/-- Quantified main-family CV divergence requiring measurable ratios and only
a.e. comparison bounds; removable-limit continuity is unnecessary. -/
theorem main_measurable_cv_unbounded (r : ℝ → ℝ → ℝ)
    (hr : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → Measurable (r ε))
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
      ∀ᵐ t ∂volume, mainRatio ε (Real.cos (t / 2) ^ 2) / 8 ≤ r ε t)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
      ∀ᵐ t ∂volume, r ε t ≤ 8 * mainRatio ε (Real.cos (t / 2) ^ 2)) (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ M < Temporal.cvSquared (r ε) := by
  apply inverse_parameter_unbounded
    (show 0 < (289 : ℝ) / (132710400 * Real.pi) by positivity)
    (by norm_num : (0 : ℝ) < 1 / 4) (fun ε => Temporal.cvSquared (r ε)) _ M
  intro ε he he'
  simpa only [div_div] using main_cv_of_measurable_envelope he he'
    (hr ε he he') (hlower ε he he') (hupper ε he he')

/-- Quantified reciprocal-family CV divergence under measurable a.e. bounds. -/
theorem reciprocal_measurable_cv_unbounded (q : ℝ → ℝ → ℝ)
    (hq : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 → Measurable (q ε))
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 →
      ∀ᵐ t ∂volume, reciprocalRatio ε (Real.cos (t / 2) ^ 2) / 8 ≤ q ε t)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 →
      ∀ᵐ t ∂volume, q ε t ≤ 8 * reciprocalRatio ε (Real.cos (t / 2) ^ 2)) (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 16 ∧ M < Temporal.cvSquared (q ε) := by
  apply inverse_parameter_unbounded
    (show 0 < (1 : ℝ) / (1679616 * Real.pi) by positivity)
    (by norm_num : (0 : ℝ) < 1 / 16) (fun ε => Temporal.cvSquared (q ε)) _ M
  intro ε he he'
  simpa only [div_div] using reciprocal_cv_of_measurable_envelope he he'
    (hq ε he he') (hlower ε he he') (hupper ε he he')

end Krylov.TemporalMeasure
