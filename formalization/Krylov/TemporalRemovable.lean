import Krylov.FiveAtomRemovable

/-!
# Genuine pointwise removable temporal ratios

The extensions below are derived from actual five-node operator complexities.
They agree with the original ratios at every nonrecurrence, are continuous and
strictly positive on all real times, and have certified finite positive
punctured limits at every integer multiple of `2π`. Both reciprocal and
purity-scaled ratios are included. Existing null-set CV results are unchanged.
-/

noncomputable section
namespace Krylov.TemporalRemovable
open Matrix MeasureTheory FiveAtomRemovable
open Krylov.FiveAtomFamilies Krylov.TemporalFamilies

/-- Continuous extension of the main family's physical `S/C` ratio. -/
def mainContinued (ε t : ℝ) : ℝ :=
  ratioExtension (ε / 10) ((1 - ε) / 10)
    (9 * ε ^ 2 / (34 * mainD ε)) (9 * (1 - ε) ^ 2 / (34 * mainD ε)) t

/-- Its finite, strictly positive value at every common recurrence. -/
def mainRecurrenceValue (ε : ℝ) : ℝ :=
  FiveAtom.m2 (ε / 10) ((1 - ε) / 10) /
    FiveAtom.m2 (9 * ε ^ 2 / (34 * mainD ε)) (9 * (1 - ε) ^ 2 / (34 * mainD ε))

def mainReciprocalContinued (ε t : ℝ) : ℝ := 1 / mainContinued ε t

def mainPurity (ε : ℝ) : ℝ := trace (TemporalStates.mainState ε * TemporalStates.mainState ε)

def mainScaledReciprocalContinued (ε t : ℝ) : ℝ := mainPurity ε * mainReciprocalContinued ε t

/-- Continuous extension of the second family's physical reciprocal `C/S`. -/
def reciprocalContinued (η t : ℝ) : ℝ :=
  ratioExtension (8 * (η ^ 2) ^ 3 / reciprocalT (η ^ 2))
    (32 * (η ^ 2) ^ 2 / reciprocalT (η ^ 2))
    (2 * (η ^ 2) ^ 3 / reciprocalN (η ^ 2)) (2 * (η ^ 2) / reciprocalN (η ^ 2)) t

def reciprocalRecurrenceValue (η : ℝ) : ℝ :=
  FiveAtom.m2 (8 * (η ^ 2) ^ 3 / reciprocalT (η ^ 2))
    (32 * (η ^ 2) ^ 2 / reciprocalT (η ^ 2)) /
  FiveAtom.m2 (2 * (η ^ 2) ^ 3 / reciprocalN (η ^ 2)) (2 * (η ^ 2) / reciprocalN (η ^ 2))

def reciprocalScaledContinued (η t : ℝ) : ℝ :=
  PhysicalTemporal.reciprocalPurity η * reciprocalContinued η t

theorem main_continuous {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    Continuous (mainContinued ε) := ratioExtension_continuous (mainState_data he he')

theorem main_positive {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (t : ℝ) :
    0 < mainContinued ε t := ratioExtension_pos (mainRoot_data he he') (mainState_data he he') t

theorem main_agrees {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (ht : Real.cos t ≠ 1) :
    PhysicalTemporal.mainRatio ε t = mainContinued ε t :=
  ratio_eq_extension (mainRoot_data he he') (mainState_data he he') ht

theorem main_at_recurrence {ε t₀ : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (ht : Real.cos t₀ = 1) :
    mainContinued ε t₀ = mainRecurrenceValue ε :=
  ratioExtension_recurrence (mainRoot_data he he') (mainState_data he he') ht

/-- Ordinary two-sided punctured limit of the original main ratio, positive and finite. -/
theorem main_removable_limit {ε t₀ : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (ht : Real.cos t₀ = 1) :
    Filter.Tendsto (PhysicalTemporal.mainRatio ε) (nhdsWithin t₀ ({t₀}ᶜ))
      (nhds (mainRecurrenceValue ε)) ∧ 0 < mainRecurrenceValue ε :=
  ratio_removable_limit (mainRoot_data he he') (mainState_data he he') ht

theorem main_limit_at_every_period {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (n : ℤ) :
    Filter.Tendsto (PhysicalTemporal.mainRatio ε)
      (nhdsWithin ((n : ℝ) * (2 * Real.pi)) ({(n : ℝ) * (2 * Real.pi)}ᶜ))
      (nhds (mainRecurrenceValue ε)) ∧ 0 < mainRecurrenceValue ε :=
  main_removable_limit he he' (Real.cos_int_mul_two_pi n)

theorem main_reciprocal_continuous {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    Continuous (mainReciprocalContinued ε) :=
  continuous_const.div (main_continuous he he') (fun t => (main_positive he he' t).ne')

theorem main_reciprocal_positive {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (t : ℝ) :
    0 < mainReciprocalContinued ε t := one_div_pos.mpr (main_positive he he' t)

theorem main_reciprocal_agrees {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (ht : Real.cos t ≠ 1) :
    mainMixed ε t / mainSpread ε t = mainReciprocalContinued ε t := by
  unfold mainReciprocalContinued
  rw [← main_agrees he he' ht]
  simp only [PhysicalTemporal.mainRatio, one_div_div]

theorem main_reciprocal_limit {ε t₀ : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (ht : Real.cos t₀ = 1) :
    Filter.Tendsto (fun t => mainMixed ε t / mainSpread ε t) (nhdsWithin t₀ ({t₀}ᶜ))
      (nhds (1 / mainRecurrenceValue ε)) ∧ 0 < 1 / mainRecurrenceValue ε := by
  have h := ratio_removable_limit (mainState_data he he') (mainRoot_data he he') ht
  simpa only [mainRecurrenceValue, one_div_div] using h

theorem mainPurity_pos {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) : 0 < mainPurity ε := by
  unfold mainPurity
  rw [TemporalStates.mainState_purity]
  have hd : 0 < mainD ε := by linarith [(mainD_bounds he he').1]
  positivity

theorem main_scaled_reciprocal_continuous {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    Continuous (mainScaledReciprocalContinued ε) := continuous_const.mul (main_reciprocal_continuous he he')

theorem main_scaled_reciprocal_positive {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (t : ℝ) :
    0 < mainScaledReciprocalContinued ε t := mul_pos (mainPurity_pos he he') (main_reciprocal_positive he he' t)

theorem main_scaled_reciprocal_limit {ε t₀ : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    (ht : Real.cos t₀ = 1) :
    Filter.Tendsto (fun t => mainPurity ε * (mainMixed ε t / mainSpread ε t))
      (nhdsWithin t₀ ({t₀}ᶜ)) (nhds (mainPurity ε * (1 / mainRecurrenceValue ε))) ∧
      0 < mainPurity ε * (1 / mainRecurrenceValue ε) := by
  have h := main_reciprocal_limit he he' ht
  exact ⟨h.1.const_mul _, mul_pos (mainPurity_pos he he') h.2⟩

theorem reciprocal_continuous {η : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16) :
    Continuous (reciprocalContinued η) := ratioExtension_continuous (reciprocalRoot_data he he')

theorem reciprocal_positive {η : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16) (t : ℝ) :
    0 < reciprocalContinued η t :=
  ratioExtension_pos (reciprocalState_data he he') (reciprocalRoot_data he he') t

theorem reciprocal_agrees {η t : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16) (ht : Real.cos t ≠ 1) :
    PhysicalTemporal.reciprocalRatio η t = reciprocalContinued η t :=
  ratio_eq_extension (reciprocalState_data he he') (reciprocalRoot_data he he') ht

theorem reciprocal_at_recurrence {η t₀ : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16)
    (ht : Real.cos t₀ = 1) : reciprocalContinued η t₀ = reciprocalRecurrenceValue η :=
  ratioExtension_recurrence (reciprocalState_data he he') (reciprocalRoot_data he he') ht

theorem reciprocal_removable_limit {η t₀ : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16)
    (ht : Real.cos t₀ = 1) :
    Filter.Tendsto (PhysicalTemporal.reciprocalRatio η) (nhdsWithin t₀ ({t₀}ᶜ))
      (nhds (reciprocalRecurrenceValue η)) ∧ 0 < reciprocalRecurrenceValue η :=
  ratio_removable_limit (reciprocalState_data he he') (reciprocalRoot_data he he') ht

theorem reciprocal_limit_at_every_period {η : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16) (n : ℤ) :
    Filter.Tendsto (PhysicalTemporal.reciprocalRatio η)
      (nhdsWithin ((n : ℝ) * (2 * Real.pi)) ({(n : ℝ) * (2 * Real.pi)}ᶜ))
      (nhds (reciprocalRecurrenceValue η)) ∧ 0 < reciprocalRecurrenceValue η :=
  reciprocal_removable_limit he he' (Real.cos_int_mul_two_pi n)

theorem reciprocal_scaled_continuous {η : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16) :
    Continuous (reciprocalScaledContinued η) := continuous_const.mul (reciprocal_continuous he he')

theorem reciprocal_scaled_positive {η : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16) (t : ℝ) :
    0 < reciprocalScaledContinued η t :=
  mul_pos (PhysicalTemporal.reciprocalPurity_pos η) (reciprocal_positive he he' t)

theorem reciprocal_scaled_limit {η t₀ : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16)
    (ht : Real.cos t₀ = 1) :
    Filter.Tendsto (fun t => PhysicalTemporal.reciprocalPurity η * PhysicalTemporal.reciprocalRatio η t)
      (nhdsWithin t₀ ({t₀}ᶜ)) (nhds (PhysicalTemporal.reciprocalPurity η * reciprocalRecurrenceValue η)) ∧
      0 < PhysicalTemporal.reciprocalPurity η * reciprocalRecurrenceValue η := by
  have h := reciprocal_removable_limit he he' ht
  exact ⟨h.1.const_mul _, mul_pos (PhysicalTemporal.reciprocalPurity_pos η) h.2⟩

/-- The existing full-period CV proofs apply unchanged to the genuine extension. -/
theorem main_cv_preserved {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    Temporal.cvSquared (mainContinued ε) = Temporal.cvSquared (PhysicalTemporal.mainRatio ε) := by
  apply TemporalMeasure.cvSquared_congr_ae
  filter_upwards [ReturnLoss.ae_nonrecurrence] with t ht
  exact (main_agrees he he' ht).symm

theorem reciprocal_cv_preserved {η : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16) :
    Temporal.cvSquared (reciprocalContinued η) = Temporal.cvSquared (PhysicalTemporal.reciprocalRatio η) := by
  apply TemporalMeasure.cvSquared_congr_ae
  filter_upwards [ReturnLoss.ae_nonrecurrence] with t ht
  exact (reciprocal_agrees he he' ht).symm

/-- Explicit piecewise description verifies the prescribed recurrence values. -/
theorem main_continued_piecewise {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (t : ℝ) :
    mainContinued ε t = if Real.cos t = 1 then mainRecurrenceValue ε else PhysicalTemporal.mainRatio ε t := by
  by_cases ht : Real.cos t = 1
  · simp only [ht, ↓reduceIte]
    exact main_at_recurrence he he' ht
  · simp only [ht, ↓reduceIte]
    exact (main_agrees he he' ht).symm

theorem reciprocal_continued_piecewise {η : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16) (t : ℝ) :
    reciprocalContinued η t =
      if Real.cos t = 1 then reciprocalRecurrenceValue η else PhysicalTemporal.reciprocalRatio η t := by
  by_cases ht : Real.cos t = 1
  · simp only [ht, ↓reduceIte]
    exact reciprocal_at_recurrence he he' ht
  · simp only [ht, ↓reduceIte]
    exact (reciprocal_agrees he he' ht).symm

theorem main_scaled_reciprocal_agrees {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    (ht : Real.cos t ≠ 1) :
    mainPurity ε * (mainMixed ε t / mainSpread ε t) = mainScaledReciprocalContinued ε t := by
  unfold mainScaledReciprocalContinued
  rw [main_reciprocal_agrees he he' ht]

theorem reciprocal_scaled_agrees {η t : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16)
    (ht : Real.cos t ≠ 1) :
    PhysicalTemporal.reciprocalPurity η * PhysicalTemporal.reciprocalRatio η t =
      reciprocalScaledContinued η t := by
  unfold reciprocalScaledContinued
  rw [reciprocal_agrees he he' ht]

theorem main_periodic (ε : ℝ) : Function.Periodic (mainContinued ε) (2 * Real.pi) :=
  ratioExtension_periodic _ _ _ _

theorem reciprocal_periodic (η : ℝ) : Function.Periodic (reciprocalContinued η) (2 * Real.pi) :=
  ratioExtension_periodic _ _ _ _

theorem main_reciprocal_cv_preserved {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    Temporal.cvSquared (mainReciprocalContinued ε) =
      Temporal.cvSquared (fun t => mainMixed ε t / mainSpread ε t) := by
  apply TemporalMeasure.cvSquared_congr_ae
  filter_upwards [ReturnLoss.ae_nonrecurrence] with t ht
  exact (main_reciprocal_agrees he he' ht).symm

theorem reciprocal_scaled_cv_preserved {η : ℝ} (he : 0 < η) (he' : η ^ 2 ≤ 1 / 16) :
    Temporal.cvSquared (reciprocalScaledContinued η) =
      Temporal.cvSquared (fun t => PhysicalTemporal.reciprocalPurity η * PhysicalTemporal.reciprocalRatio η t) := by
  apply TemporalMeasure.cvSquared_congr_ae
  filter_upwards [ReturnLoss.ae_nonrecurrence] with t ht
  exact (reciprocal_scaled_agrees he he' ht).symm

end Krylov.TemporalRemovable
