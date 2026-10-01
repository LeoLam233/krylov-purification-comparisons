import Krylov.FamilySourceAPI

namespace Krylov.SourceMomentBounds
open MeasureTheory TemporalMeasure TemporalFamilies
noncomputable section
set_option maxHeartbeats 1000000

/-! Export the separately displayed first/second-moment bounds from the
continuous-envelope argument, then instantiate them with the actual GS ratios. -/
theorem main_moments_of_envelope {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    {r : ℝ → ℝ} (hr : Measurable r)
    (hlower : ∀ᵐ t ∂volume, mainRatio ε (Real.cos (t / 2) ^ 2) / 8 ≤ r t)
    (hupper : ∀ᵐ t ∂volume, r t ≤ 8 * mainRatio ε (Real.cos (t / 2) ^ 2)) :
    0 < Temporal.periodMean r ∧ Temporal.periodMean r ≤ 8 ∧
    289/(2073600*Real.pi*ε) ≤ Temporal.periodMean (fun t => r t^2) := by
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
  exact ⟨hμ,hμupper,hmoment⟩

theorem reciprocal_moments_of_envelope {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16)
    {q : ℝ → ℝ} (hq : Measurable q)
    (hlower : ∀ᵐ t ∂volume, reciprocalRatio ε (Real.cos (t / 2) ^ 2) / 8 ≤ q t)
    (hupper : ∀ᵐ t ∂volume, q t ≤ 8 * reciprocalRatio ε (Real.cos (t / 2) ^ 2)) :
    0 < Temporal.periodMean q ∧ Temporal.periodMean q ≤ 216*ε ∧
    ε/(36*Real.pi) ≤ Temporal.periodMean (fun t => q t^2) := by
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
  exact ⟨hμ,hμupper,hmoment⟩


theorem main_envelope {ε t : ℝ} (he : 0<ε) (he' : ε≤1/4) (ht : Real.cos t ≠ 1) :
    mainRatio ε (Real.cos (t/2)^2)/8 ≤ FamilySourceAPI.mainContinued ε t ∧
      FamilySourceAPI.mainContinued ε t ≤ 8*mainRatio ε (Real.cos (t/2)^2) := by
  rw [FamilySourceAPI.mainContinued,if_neg ht,FamilySourceAPI.mainRatio_eq he he']
  have hp := ReturnLoss.main_losses_pos he he' ht
  have h := ReturnLoss.scalar_ratio_envelope hp.1 hp.2
    (FiveAtomFamilies.mainSpread_loss_bounds he he' t)
    (FiveAtomFamilies.mainMixed_loss_bounds he he' t)
  rw [ReturnLoss.main_loss_ratio he he' ht] at h
  exact h

theorem reciprocal_envelope {η t : ℝ} (he : 0<η) (he' : η^2≤1/16)
    (ht : Real.cos t ≠ 1) :
    reciprocalRatio (η^2) (Real.cos (t/2)^2)/8 ≤ FamilySourceAPI.reciprocalContinued η t ∧
      FamilySourceAPI.reciprocalContinued η t ≤ 8*reciprocalRatio (η^2) (Real.cos (t/2)^2) := by
  rw [FamilySourceAPI.reciprocalContinued,if_neg ht,FamilySourceAPI.reciprocalRatio_eq he he']
  have hp := ReturnLoss.return_losses_pos (sq_pos_of_pos he) he' ht
  have h := ReturnLoss.scalar_ratio_envelope hp.2.2.2 hp.2.2.1
    (FiveAtomFamilies.reciprocalMixed_loss_bounds he he' t)
    (FiveAtomFamilies.reciprocalSpread_loss_bounds he he' t)
  rw [ReturnLoss.reciprocal_loss_ratio (sq_pos_of_pos he) he' ht] at h
  exact h

theorem main_source_moments {ε : ℝ} (he : 0<ε) (he' : ε≤1/4) :
    0 < Temporal.periodMean (FamilySourceAPI.mainContinued ε) ∧
    Temporal.periodMean (FamilySourceAPI.mainContinued ε) ≤ 8 ∧
    289/(2073600*Real.pi*ε) ≤
      Temporal.periodMean (fun t => FamilySourceAPI.mainContinued ε t^2) := by
  apply main_moments_of_envelope he he' (FamilySourceAPI.main_continued_continuous he he').measurable
  · filter_upwards [ReturnLoss.ae_nonrecurrence] with t ht
    exact (main_envelope he he' ht).1
  · filter_upwards [ReturnLoss.ae_nonrecurrence] with t ht
    exact (main_envelope he he' ht).2

theorem reciprocal_source_moments {η : ℝ} (he : 0<η) (he' : η^2≤1/16) :
    0 < Temporal.periodMean (FamilySourceAPI.reciprocalContinued η) ∧
    Temporal.periodMean (FamilySourceAPI.reciprocalContinued η) ≤ 216*η^2 ∧
    η^2/(36*Real.pi) ≤
      Temporal.periodMean (fun t => FamilySourceAPI.reciprocalContinued η t^2) := by
  apply reciprocal_moments_of_envelope (sq_pos_of_pos he) he'
    (FamilySourceAPI.reciprocal_continued_continuous he he').measurable
  · filter_upwards [ReturnLoss.ae_nonrecurrence] with t ht
    exact (reciprocal_envelope he he' ht).1
  · filter_upwards [ReturnLoss.ae_nonrecurrence] with t ht
    exact (reciprocal_envelope he he' ht).2

lemma nonrecurrence_on_window {ε t : ℝ} (he : 0<ε) (he' : ε≤1/4)
    (ht : t ∈ Set.Icc (Real.pi-ε) (Real.pi+ε)) : Real.cos t ≠ 1 := by
  intro hc
  have hp := cos_half_peak he.le ht
  have ht2 : 2*(t/2)=t := by ring
  have hcos := Real.cos_two_mul (t/2)
  rw [ht2,hc] at hcos
  nlinarith

theorem main_source_window {ε t : ℝ} (he : 0<ε) (he' : ε≤1/4)
    (ht : t ∈ Set.Icc (Real.pi-ε) (Real.pi+ε)) :
    17/(1440*ε) ≤ FamilySourceAPI.mainContinued ε t := by
  have hp := (main_envelope he he' (nonrecurrence_on_window he he' ht)).1
  have hw := mainRatio_time_peak he he' ht
  have hdiv := div_le_div_of_nonneg_right hw (by norm_num : (0:ℝ)≤8)
  have hx : (17/(180*ε))/8 = 17/(1440*ε) := by ring
  rw [hx] at hdiv
  exact hdiv.trans hp

theorem reciprocal_source_window {η t : ℝ} (he : 0<η) (he' : η^2≤1/16)
    (ht : t ∈ Set.Icc (Real.pi-η^2) (Real.pi+η^2)) :
    1/6 ≤ FamilySourceAPI.reciprocalContinued η t := by
  have hp := (reciprocal_envelope he he'
    (nonrecurrence_on_window (sq_pos_of_pos he) (by linarith) ht)).1
  have hw := reciprocalRatio_time_peak (sq_pos_of_pos he) he' ht
  have hdiv := div_le_div_of_nonneg_right hw (by norm_num : (0:ℝ)≤8)
  norm_num at hdiv
  exact hdiv.trans hp

end
end Krylov.SourceMomentBounds
