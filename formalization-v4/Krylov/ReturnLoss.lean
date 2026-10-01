import Krylov.TemporalMeasure

/-!
# Recurrence-aware return-loss cancellation

The four displayed temporal return losses are positive off the countable
common recurrence set. Their quotients equal the continuous rational profiles
used in the period-mean and CV arguments. These are exact algebraic/trigonometric
identities and do not presume a Krylov-complexity identification.
-/

noncomputable section
namespace Krylov.ReturnLoss
open MeasureTheory
open Krylov.TemporalFamilies

def mainSpreadLoss (ε t : ℝ) : ℝ :=
  ((1 - ε) * (1 - Real.cos (2 * t)) + ε * (1 - Real.cos t)) / 10

def mainMixedLoss (ε t : ℝ) : ℝ :=
  (9 / (34 * mainD ε)) *
    ((1 - ε) ^ 2 * (1 - Real.cos (2 * t)) + ε ^ 2 * (1 - Real.cos t))

def reciprocalSpreadLoss (ε t : ℝ) : ℝ :=
  (2 * ε / reciprocalN ε) * (1 - Real.cos (2 * t)) +
    (2 * ε ^ 3 / reciprocalN ε) * (1 - Real.cos t)

def reciprocalMixedLoss (ε t : ℝ) : ℝ :=
  (32 * ε ^ 2 / reciprocalT ε) * (1 - Real.cos (2 * t)) +
    (8 * ε ^ 3 / reciprocalT ε) * (1 - Real.cos t)

def recurrences : Set ℝ := {t | Real.cos t = 1}

theorem recurrences_countable : recurrences.Countable := by
  have heq : recurrences = Set.range (fun n : ℤ => (n : ℝ) * (2 * Real.pi)) := by
    ext t
    exact Real.cos_eq_one_iff t
  rw [heq]
  exact Set.countable_range _

theorem ae_nonrecurrence : ∀ᵐ t ∂volume, Real.cos t ≠ 1 :=
  recurrences_countable.ae_not_mem volume

theorem double_gap_factor (t : ℝ) :
    1 - Real.cos (2 * t) = 4 * Real.cos (t / 2) ^ 2 * (1 - Real.cos t) := by
  have hhalf : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (t / 2) using 1
    congr 1
    ring
  rw [Real.cos_two_mul, hhalf]
  ring

theorem return_losses_pos {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16)
    (ht : Real.cos t ≠ 1) :
    0 < mainSpreadLoss ε t ∧ 0 < mainMixedLoss ε t ∧
      0 < reciprocalSpreadLoss ε t ∧ 0 < reciprocalMixedLoss ε t := by
  have hεquarter : ε ≤ 1 / 4 := by linarith
  have hd : 0 < mainD ε := by linarith [(mainD_bounds he hεquarter).1]
  have htr := reciprocal_trace_bounds he he'
  have hn : 0 < reciprocalN ε := by linarith [htr.1]
  have hT : 0 < reciprocalT ε := by linarith [htr.2.2.1]
  have hcos : 0 < 1 - Real.cos t := by
    have hle := Real.cos_le_one t
    exact sub_pos.mpr (lt_of_le_of_ne hle ht)
  have hcos2 : 0 ≤ 1 - Real.cos (2 * t) := sub_nonneg.mpr (Real.cos_le_one _)
  have he1 : 0 < 1 - ε := by linarith
  unfold mainSpreadLoss mainMixedLoss reciprocalSpreadLoss reciprocalMixedLoss
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem main_losses_pos {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    (ht : Real.cos t ≠ 1) : 0 < mainSpreadLoss ε t ∧ 0 < mainMixedLoss ε t := by
  have hd : 0 < mainD ε := by linarith [(mainD_bounds he he').1]
  have hcos : 0 < 1 - Real.cos t := by
    exact sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one t) ht)
  have hcos2 : 0 ≤ 1 - Real.cos (2 * t) := sub_nonneg.mpr (Real.cos_le_one _)
  have he1 : 0 < 1 - ε := by linarith
  unfold mainSpreadLoss mainMixedLoss
  constructor <;> positivity

/-- Exact cancellation of the common recurrence factor in the main ratio. -/
theorem main_loss_ratio {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    (ht : Real.cos t ≠ 1) :
    mainSpreadLoss ε t / mainMixedLoss ε t = mainRatio ε (Real.cos (t / 2) ^ 2) := by
  have hd : mainD ε ≠ 0 := by linarith [(mainD_bounds he he').1]
  have hb : 1 - Real.cos t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hden : 4 * (1 - ε) ^ 2 * Real.cos (t / 2) ^ 2 + ε ^ 2 ≠ 0 :=
    ne_of_gt (mainRatio_denominator_pos he (sq_nonneg _))
  have hs : mainSpreadLoss ε t = (1 - Real.cos t) / 10 *
      (4 * (1 - ε) * Real.cos (t / 2) ^ 2 + ε) := by
    unfold mainSpreadLoss
    rw [double_gap_factor]
    ring
  have hk : mainMixedLoss ε t = (9 * (1 - Real.cos t) / (34 * mainD ε)) *
      (4 * (1 - ε) ^ 2 * Real.cos (t / 2) ^ 2 + ε ^ 2) := by
    unfold mainMixedLoss
    rw [double_gap_factor]
    ring
  rw [hs, hk]
  unfold mainRatio
  field_simp
  ring

/-- Exact cancellation in the reciprocal ratio. -/
theorem reciprocal_loss_ratio {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16)
    (ht : Real.cos t ≠ 1) :
    reciprocalMixedLoss ε t / reciprocalSpreadLoss ε t =
      reciprocalRatio ε (Real.cos (t / 2) ^ 2) := by
  have htr := reciprocal_trace_bounds he he'
  have hn : reciprocalN ε ≠ 0 := by linarith [htr.1]
  have hT : reciprocalT ε ≠ 0 := by linarith [htr.2.2.1]
  have he0 : ε ≠ 0 := ne_of_gt he
  have hb : 1 - Real.cos t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hden : 4 * Real.cos (t / 2) ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have hs : reciprocalSpreadLoss ε t = (2 * ε * (1 - Real.cos t) / reciprocalN ε) *
      (4 * Real.cos (t / 2) ^ 2 + ε ^ 2) := by
    unfold reciprocalSpreadLoss
    rw [double_gap_factor]
    ring
  have hk : reciprocalMixedLoss ε t = (8 * ε ^ 2 * (1 - Real.cos t) / reciprocalT ε) *
      (16 * Real.cos (t / 2) ^ 2 + ε) := by
    unfold reciprocalMixedLoss
    rw [double_gap_factor]
    ring
  rw [hs, hk]
  unfold reciprocalRatio
  field_simp
  ring

theorem main_loss_ratio_ae {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    (fun t => mainSpreadLoss ε t / mainMixedLoss ε t) =ᵐ[volume]
      (fun t => mainRatio ε (Real.cos (t / 2) ^ 2)) := by
  filter_upwards [ae_nonrecurrence] with t ht
  exact main_loss_ratio he he' ht

theorem reciprocal_loss_ratio_ae {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16) :
    (fun t => reciprocalMixedLoss ε t / reciprocalSpreadLoss ε t) =ᵐ[volume]
      (fun t => reciprocalRatio ε (Real.cos (t / 2) ^ 2)) := by
  filter_upwards [ae_nonrecurrence] with t ht
  exact reciprocal_loss_ratio he he' ht

/-- Pure algebra transporting the dimension-five return-loss comparison to
ratio envelopes. No regularity or nonzero-complexity assumption is hidden. -/
theorem scalar_ratio_envelope {A B X Y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hX : A ≤ X ∧ X ≤ 8 * A) (hY : B ≤ Y ∧ Y ≤ 8 * B) :
    (A / B) / 8 ≤ X / Y ∧ X / Y ≤ 8 * (A / B) := by
  have hY0 : 0 < Y := lt_of_lt_of_le hB hY.1
  constructor
  · rw [div_div]
    apply (div_le_div_iff₀ (by positivity) hY0).2
    have h1 := mul_le_mul_of_nonneg_left hY.2 (le_of_lt hA)
    have h2 := mul_le_mul_of_nonneg_right hX.1 (show 0 ≤ 8 * B by positivity)
    nlinarith
  · have heq : 8 * (A / B) = (8 * A) / B := by ring
    rw [heq]
    apply (div_le_div_iff₀ hY0 hB).2
    have h1 := mul_le_mul_of_nonneg_right hX.2 (le_of_lt hB)
    have h2 := mul_le_mul_of_nonneg_left hY.1 (show 0 ≤ 8 * A by positivity)
    nlinarith

/-- Direct usable CV theorem once the actual main-family complexities have
been compared to their two return losses by the finite-chain bound. -/
theorem main_cv_of_loss_bounds {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    {CS CK : ℝ → ℝ} (hCS : Measurable CS) (hCK : Measurable CK)
    (hS : ∀ t : ℝ, mainSpreadLoss ε t ≤ CS t ∧ CS t ≤ 8 * mainSpreadLoss ε t)
    (hK : ∀ t : ℝ, mainMixedLoss ε t ≤ CK t ∧ CK t ≤ 8 * mainMixedLoss ε t) :
    289 / (132710400 * Real.pi * ε) - 1 ≤ Temporal.cvSquared (fun t => CS t / CK t) := by
  apply TemporalMeasure.main_cv_of_measurable_envelope he he' (hCS.div hCK)
  · filter_upwards [ae_nonrecurrence] with t ht
    have hp := main_losses_pos he he' ht
    have h := (scalar_ratio_envelope hp.1 hp.2 (hS t) (hK t)).1
    rwa [main_loss_ratio he he' ht] at h
  · filter_upwards [ae_nonrecurrence] with t ht
    have hp := main_losses_pos he he' ht
    have h := (scalar_ratio_envelope hp.1 hp.2 (hS t) (hK t)).2
    rwa [main_loss_ratio he he' ht] at h

/-- Corresponding direct CV theorem for the reciprocal of the complexities. -/
theorem reciprocal_cv_of_loss_bounds {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16)
    {CS CK : ℝ → ℝ} (hCS : Measurable CS) (hCK : Measurable CK)
    (hS : ∀ t : ℝ, reciprocalSpreadLoss ε t ≤ CS t ∧ CS t ≤ 8 * reciprocalSpreadLoss ε t)
    (hK : ∀ t : ℝ, reciprocalMixedLoss ε t ≤ CK t ∧ CK t ≤ 8 * reciprocalMixedLoss ε t) :
    1 / (1679616 * Real.pi * ε) - 1 ≤ Temporal.cvSquared (fun t => CK t / CS t) := by
  apply TemporalMeasure.reciprocal_cv_of_measurable_envelope he he' (hCK.div hCS)
  · filter_upwards [ae_nonrecurrence] with t ht
    have hp := return_losses_pos he he' ht
    have h := (scalar_ratio_envelope hp.2.2.2 hp.2.2.1 (hK t) (hS t)).1
    rwa [reciprocal_loss_ratio he he' ht] at h
  · filter_upwards [ae_nonrecurrence] with t ht
    have hp := return_losses_pos he he' ht
    have h := (scalar_ratio_envelope hp.2.2.2 hp.2.2.1 (hK t) (hS t)).2
    rwa [reciprocal_loss_ratio he he' ht] at h

/-- The normalized return amplitude of a symmetric five-node measure with
total gap-one and gap-two masses `u` and `v`. -/
def fiveReturnAmplitude (u v t : ℝ) : ℝ := 1 - u - v + u * Real.cos t + v * Real.cos (2 * t)

theorem five_return_amplitude_bounds {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hmass : u + v ≤ 1 / 2) (t : ℝ) :
    0 ≤ fiveReturnAmplitude u v t ∧ fiveReturnAmplitude u v t ≤ 1 := by
  have h1 := mul_nonneg hu (sub_nonneg.mpr (Real.cos_le_one t))
  have h2 := mul_nonneg hv (sub_nonneg.mpr (Real.cos_le_one (2 * t)))
  have h3 := mul_nonneg hu (show 0 ≤ 1 + Real.cos t by linarith [Real.neg_one_le_cos t])
  have h4 := mul_nonneg hv (show 0 ≤ 1 + Real.cos (2 * t) by linarith [Real.neg_one_le_cos (2 * t)])
  unfold fiveReturnAmplitude
  constructor <;> nlinarith

theorem main_mass_bounds {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    ε / 10 + (1 - ε) / 10 ≤ 1 / 2 ∧
      9 * ε ^ 2 / (34 * mainD ε) + 9 * (1 - ε) ^ 2 / (34 * mainD ε) ≤ 1 / 2 := by
  constructor
  · linarith
  · have hd : 0 < mainD ε := by linarith [(mainD_bounds he he').1]
    rw [← add_div]
    apply (div_le_iff₀ (by positivity : 0 < 34 * mainD ε)).2
    unfold mainD
    nlinarith [sq_nonneg ε, sq_nonneg (1 - ε)]

theorem reciprocal_mass_bounds {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16) :
    2 * ε ^ 3 / reciprocalN ε + 2 * ε / reciprocalN ε ≤ 1 / 2 ∧
      8 * ε ^ 3 / reciprocalT ε + 32 * ε ^ 2 / reciprocalT ε ≤ 1 / 2 := by
  have ht := reciprocal_trace_bounds he he'
  have hn : 0 < reciprocalN ε := by linarith [ht.1]
  have hT : 0 < reciprocalT ε := by linarith [ht.2.2.1]
  have h3 := pow_le_pow_left₀ (le_of_lt he) he' 3
  norm_num at h3
  constructor
  · rw [← add_div]
    apply (div_le_iff₀ hn).2
    unfold reciprocalN
    nlinarith
  · rw [← add_div]
    apply (div_le_iff₀ hT).2
    unfold reciprocalT
    nlinarith [sq_nonneg ε, pow_nonneg (le_of_lt he) 6]

theorem mainSpreadLoss_eq_return (ε t : ℝ) :
    mainSpreadLoss ε t = 1 - fiveReturnAmplitude (ε / 10) ((1 - ε) / 10) t := by
  unfold mainSpreadLoss fiveReturnAmplitude
  ring

theorem mainMixedLoss_eq_return (ε t : ℝ) :
    mainMixedLoss ε t = 1 - fiveReturnAmplitude
      (9 * ε ^ 2 / (34 * mainD ε)) (9 * (1 - ε) ^ 2 / (34 * mainD ε)) t := by
  unfold mainMixedLoss fiveReturnAmplitude
  ring

theorem reciprocalSpreadLoss_eq_return (ε t : ℝ) :
    reciprocalSpreadLoss ε t = 1 - fiveReturnAmplitude
      (2 * ε ^ 3 / reciprocalN ε) (2 * ε / reciprocalN ε) t := by
  unfold reciprocalSpreadLoss fiveReturnAmplitude
  ring

theorem reciprocalMixedLoss_eq_return (ε t : ℝ) :
    reciprocalMixedLoss ε t = 1 - fiveReturnAmplitude
      (8 * ε ^ 3 / reciprocalT ε) (32 * ε ^ 2 / reciprocalT ε) t := by
  unfold reciprocalMixedLoss fiveReturnAmplitude
  ring

/-- Half-angle zero and the period recurrence condition are equivalent. -/
theorem sin_half_zero_iff_recurrence (t : ℝ) : Real.sin (t / 2) = 0 ↔ Real.cos t = 1 := by
  have hcos : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (t / 2) using 1
    congr 1
    ring
  have hsc := Real.sin_sq_add_cos_sq (t / 2)
  constructor
  · intro hs
    rw [hs] at hsc
    nlinarith
  · intro hc
    nlinarith [sq_nonneg (Real.sin (t / 2))]

/-- The excluded times are exactly the integer multiples of the common period. -/
theorem sin_half_zero_iff_period (t : ℝ) :
    Real.sin (t / 2) = 0 ↔ ∃ n : ℤ, (n : ℝ) * (2 * Real.pi) = t := by
  rw [sin_half_zero_iff_recurrence, Real.cos_eq_one_iff]

end Krylov.ReturnLoss
