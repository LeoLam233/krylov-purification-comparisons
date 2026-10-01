import Krylov.ThreeAtomOperator
import Krylov.ReturnLoss

/-!
# Source-level physical consequences of the three-atom bridge

All complexities below are defined by `ThreeAtomOperator` through actual
commutator chains and diagonal-unitary matrix evolution. The time-domain
qutrit comparison/asymptotic and fixed-purity recurrence-period mean statements
are consequently physical operator claims, not conditional spectral formulas.
-/

noncomputable section
namespace Krylov.PhysicalRatios
open Matrix MeasureTheory
open Krylov.Ratios Krylov.FamilyStates Krylov.ThreeAtomOperator

/-- Strict all-time qutrit comparison at every nonrecurrence. -/
theorem qutrit_all_time_strict {m t : ℝ} (hm : 4 ≤ m) (ht : Real.sin (t / 2) ≠ 0) :
    qutritMixed m t < qutritSpread m t := by
  rw [qutritMixed_eq hm, qutritSpread_eq hm, threeAtom_time_eq, threeAtom_time_eq]
  have hz : 16 ≤ m ^ 2 := by nlinarith
  exact qutrit_strict_order hz (sq_pos_of_ne_zero ht) (Real.sin_sq_le_one _)

theorem qutrit_peak_ratio {m : ℝ} (hm : 4 ≤ m) :
    qutritSpread m Real.pi / qutritMixed m Real.pi = qutritPeakRatio (m ^ 2) := by
  rw [qutritSpread_eq hm, qutritMixed_eq hm, threeAtom_time_eq, threeAtom_time_eq]
  simp only [Real.sin_pi_div_two, one_pow]
  exact (qutrit_peak_ratio_eq _).symm

/-- Exact physical asymptotic coefficient of the qutrit family. -/
theorem qutrit_physical_asymptotic :
    Filter.Tendsto (fun m : ℝ => (qutritSpread m Real.pi / qutritMixed m Real.pi) / m ^ 2)
      Filter.atTop (nhds (1 / 9 : ℝ)) := by
  apply qutrit_peak_asymptotic_m.congr'
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ)] with m hm
  rw [qutrit_peak_ratio hm]

/-- Actual physical ratio with its prescribed removable recurrence values. -/
def fixedContinuedRatio (ε t : ℝ) : ℝ :=
  if Real.sin (t / 2) = 0 then 5 / (18 * ε) else fixedSpread ε t / fixedMixed ε t

/-- The continued physical ratio equals the rational scalar expression at all times. -/
theorem fixedContinuedRatio_eq {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) (t : ℝ) :
    fixedContinuedRatio ε t = fixedPurityRatio ε (Real.sin (t / 2) ^ 2) := by
  by_cases ht : Real.sin (t / 2) = 0
  · simp [fixedContinuedRatio, ht, fixedPurityRatio]
  · simp only [fixedContinuedRatio, ht, ↓reduceIte]
    exact fixed_operator_quotient he he' ht

/-- In particular, the recurrence assignment is genuinely a continuous extension. -/
theorem fixedContinuedRatio_continuous {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    Continuous (fixedContinuedRatio ε) := by
  have hfun : fixedContinuedRatio ε =
      (fun t : ℝ => fixedPurityRatio ε (Real.sin (t / 2) ^ 2)) := by
    funext t
    exact fixedContinuedRatio_eq he he' t
  rw [hfun]
  unfold fixedPurityRatio
  apply continuous_const.mul
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    exact ne_of_gt (fixedPurity_denominator_pos he he' (sq_nonneg _))

/-- Both explicit source bounds hold for the actual continued physical ratio. -/
theorem fixed_physical_uniform_bounds {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) (t : ℝ) :
    (5 / (18 * ε)) * (1 - ε / 10) ≤ fixedContinuedRatio ε t ∧
      fixedContinuedRatio ε t ≤ 5 / (18 * ε) := by
  rw [fixedContinuedRatio_eq he he']
  exact fixedPurity_bounds he he' (sq_nonneg _) (Real.sin_sq_le_one _)

theorem periodMean_constant (c : ℝ) : Temporal.periodMean (fun _ => c) = c := by
  unfold Temporal.periodMean
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  field_simp

/-- The same uniform two-sided bounds hold for the actual period mean. -/
theorem fixed_physical_periodMean_bounds {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    (5 / (18 * ε)) * (1 - ε / 10) ≤ Temporal.periodMean (fixedContinuedRatio ε) ∧
      Temporal.periodMean (fixedContinuedRatio ε) ≤ 5 / (18 * ε) := by
  have hc := fixedContinuedRatio_continuous he he'
  have hlo := TemporalFamilies.periodMean_mono continuous_const hc
    (fun t => (fixed_physical_uniform_bounds he he' t).1)
  have hhi := TemporalFamilies.periodMean_mono hc continuous_const
    (fun t => (fixed_physical_uniform_bounds he he' t).2)
  rw [periodMean_constant] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- No finite purity-only upper bound exists even for the actual recurrence-period
mean. Every selected witness is a positive, unit-trace, exactly purity-1/2 matrix. -/
theorem fixed_physical_periodMean_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 5 / 18 ∧ (fixedState ε).PosDef ∧
      trace (fixedState ε) = 1 ∧ trace (fixedState ε * fixedState ε) = 1 / 2 ∧
      M < Temporal.periodMean (fixedContinuedRatio ε) := by
  obtain ⟨ε, he, he', h⟩ := fixedPurity_uniform_unbounded (M + 1)
  refine ⟨ε, he, he', fixedState_posDef he he', fixedState_trace ε,
    fixedState_purity he he', ?_⟩
  have hc := fixedContinuedRatio_continuous he he'
  have hl := TemporalFamilies.periodMean_mono continuous_const hc (fun t => by
    rw [fixedContinuedRatio_eq he he']
    exact le_of_lt (h _ (sq_nonneg _) (Real.sin_sq_le_one _)))
  rw [periodMean_constant] at hl
  linarith

/-- The continued reciprocal obeys an explicit uniform bound tending to zero. -/
theorem fixed_physical_reciprocal_bounds {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) (t : ℝ) :
    0 < 1 / fixedContinuedRatio ε t ∧ 1 / fixedContinuedRatio ε t ≤ 4 * ε := by
  rw [fixedContinuedRatio_eq he he']
  exact fixedPurity_reciprocal_bounds he he' (sq_nonneg _) (Real.sin_sq_le_one _)

/-- Uniform convergence-to-zero formulation for the actual reciprocal ratios. -/
theorem fixed_physical_reciprocal_uniform_small {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < 5 / 18 →
      ∀ t : ℝ, 0 < 1 / fixedContinuedRatio ε t ∧ 1 / fixedContinuedRatio ε t < δ := by
  refine ⟨δ / 4, by positivity, ?_⟩
  intro ε he heδ he' t
  have h := fixed_physical_reciprocal_bounds he he' t
  exact ⟨h.1, lt_of_le_of_lt h.2 (by linarith)⟩

end Krylov.PhysicalRatios
