import Krylov.PeriodIntegral
import Krylov.Temporal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Exact analytic-family algebra for the temporal CV constructions

These theorems establish the actual mean integrals and peak windows for the
rational return-loss ratios. `PeriodIntegral` supplies the proved analytic
identity. The CV-transfer results explicitly require continuity and a
comparison envelope; identifying a physical Krylov ratio with such a function
is a separate obligation.
-/

noncomputable section
namespace Krylov.TemporalFamilies

def mainD (ε : ℝ) : ℝ := (1 - ε) ^ 2 + ε ^ 2

def mainRatio (ε c : ℝ) : ℝ :=
  (17 * mainD ε / 45) * ((4 * (1 - ε) * c + ε) / (4 * (1 - ε) ^ 2 * c + ε ^ 2))

def mainMeanFormula (ε : ℝ) : ℝ :=
  (17 * mainD ε / (45 * (1 - ε))) *
    (1 + (1 - 2 * ε) / Real.sqrt (4 * (1 - ε) ^ 2 + ε ^ 2))

def reciprocalN (ε : ℝ) : ℝ := 2 + 10 * ε + 2 * ε ^ 3

def reciprocalT (ε : ℝ) : ℝ := 2 + 82 * ε ^ 2 + 12 * ε ^ 3 + 2 * ε ^ 6

def reciprocalRatio (ε c : ℝ) : ℝ :=
  (4 * reciprocalN ε * ε / reciprocalT ε) * ((16 * c + ε) / (4 * c + ε ^ 2))

def reciprocalMeanFormula (ε : ℝ) : ℝ :=
  (4 * reciprocalN ε * ε / reciprocalT ε) *
    (4 + (1 - 4 * ε) / Real.sqrt (4 + ε ^ 2))

theorem mainD_bounds {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    1 / 2 ≤ mainD ε ∧ mainD ε ≤ 1 := by
  unfold mainD
  have hp : 0 ≤ ε * (1 - ε) := mul_nonneg (le_of_lt he) (by linarith)
  constructor <;> nlinarith [sq_nonneg (ε - 1 / 2)]

/-- The manuscript's mean upper bound, for the exact closed mean formula. -/
theorem mainMeanFormula_bound {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    mainMeanFormula ε ≤ 68 / 81 := by
  have hd := mainD_bounds he he'
  have hp : 0 < 45 * (1 - ε) := by linarith
  have hs : 3 / 2 ≤ Real.sqrt (4 * (1 - ε) ^ 2 + ε ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hs0 : 0 < Real.sqrt (4 * (1 - ε) ^ 2 + ε ^ 2) := by linarith
  have hpre : 17 * mainD ε / (45 * (1 - ε)) ≤ 68 / 135 := by
    apply (div_le_iff₀ hp).2
    nlinarith
  have hbr : 1 + (1 - 2 * ε) / Real.sqrt (4 * (1 - ε) ^ 2 + ε ^ 2) ≤ 5 / 3 := by
    have hdiv : (1 - 2 * ε) / Real.sqrt (4 * (1 - ε) ^ 2 + ε ^ 2) ≤ 2 / 3 := by
      apply (div_le_iff₀ hs0).2
      linarith
    linarith
  have hbr0 : 0 ≤ 1 + (1 - 2 * ε) / Real.sqrt (4 * (1 - ε) ^ 2 + ε ^ 2) := by
    have : 0 ≤ 1 - 2 * ε := by linarith
    positivity
  have h := mul_le_mul hpre hbr hbr0 (by norm_num : (0 : ℝ) ≤ 68 / 135)
  norm_num at h
  exact h

theorem mainRatio_denominator_pos {ε c : ℝ} (he : 0 < ε) (hc : 0 ≤ c) :
    0 < 4 * (1 - ε) ^ 2 * c + ε ^ 2 := by positivity

/-- Exact rational peak estimate, with no asymptotic notation. -/
theorem mainRatio_peak {ε c : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    (hc : 0 ≤ c) (hc' : c ≤ ε ^ 2 / 4) :
    17 / (180 * ε) ≤ mainRatio ε c := by
  have hd := mainD_bounds he he'
  have hden := mainRatio_denominator_pos he hc
  have hnum : ε ≤ 4 * (1 - ε) * c + ε := by
    have : 0 ≤ 4 * (1 - ε) * c := by
      have : 0 ≤ 1 - ε := by linarith
      positivity
    linarith
  have hdenupper : 4 * (1 - ε) ^ 2 * c + ε ^ 2 ≤ 2 * ε ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hc' (show 0 ≤ 4 * (1 - ε) ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right (show (1 - ε) ^ 2 ≤ 1 by nlinarith)
      (sq_nonneg ε)
    nlinarith
  have hfrac : 1 / (2 * ε) ≤
      (4 * (1 - ε) * c + ε) / (4 * (1 - ε) ^ 2 * c + ε ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) hden).2
    nlinarith
  have hpre : 17 / 90 ≤ 17 * mainD ε / 45 := by linarith
  have hpre0 : 0 ≤ 17 * mainD ε / 45 := by
    have : 0 < mainD ε := by linarith
    positivity
  have h := mul_le_mul hpre hfrac (by positivity : 0 ≤ 1 / (2 * ε)) hpre0
  have he0 : ε ≠ 0 := ne_of_gt he
  have hval : (17 / 90 : ℝ) * (1 / (2 * ε)) = 17 / (180 * ε) := by ring
  rw [hval] at h
  exact h

/-- The trigonometric peak window required by both temporal constructions. -/
theorem cos_half_peak {ε t : ℝ} (_he : 0 ≤ ε)
    (ht : t ∈ Set.Icc (Real.pi - ε) (Real.pi + ε)) :
    Real.cos (t / 2) ^ 2 ≤ ε ^ 2 / 4 := by
  have heq : Real.cos (t / 2) ^ 2 = Real.sin ((t - Real.pi) / 2) ^ 2 := by
    have ht' : t / 2 = (t - Real.pi) / 2 + Real.pi / 2 := by ring
    rw [ht', Real.cos_add]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  rw [heq]
  have hs : Real.sin ((t - Real.pi) / 2) ^ 2 ≤ ((t - Real.pi) / 2) ^ 2 :=
    Real.sin_sq_le_sq
  have hp := mul_nonneg (show 0 ≤ ε - (t - Real.pi) by linarith [ht.2])
    (show 0 ≤ ε + (t - Real.pi) by linarith [ht.1])
  nlinarith

theorem mainRatio_time_peak {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    (ht : t ∈ Set.Icc (Real.pi - ε) (Real.pi + ε)) :
    17 / (180 * ε) ≤ mainRatio ε (Real.cos (t / 2) ^ 2) :=
  mainRatio_peak he he' (sq_nonneg _) (cos_half_peak (le_of_lt he) ht)

theorem reciprocal_trace_bounds {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16) :
    2 ≤ reciprocalN ε ∧ reciprocalN ε ≤ 3 ∧
      2 ≤ reciprocalT ε ∧ reciprocalT ε ≤ 3 := by
  have h2 := pow_le_pow_left₀ (le_of_lt he) he' 2
  have h3 := pow_le_pow_left₀ (le_of_lt he) he' 3
  have h6 := pow_le_pow_left₀ (le_of_lt he) he' 6
  norm_num at h2 h3 h6
  have h3pos : 0 ≤ ε ^ 3 := by positivity
  have h6pos : 0 ≤ ε ^ 6 := by positivity
  unfold reciprocalN reciprocalT
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith [sq_nonneg ε]
  · nlinarith

/-- The reciprocal family's exact closed mean expression is at most `27 ε`. -/
theorem reciprocalMeanFormula_bound {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16) :
    reciprocalMeanFormula ε ≤ 27 * ε := by
  have ht := reciprocal_trace_bounds he he'
  have hT : 0 < reciprocalT ε := by linarith [ht.2.2.1]
  have hs : 2 ≤ Real.sqrt (4 + ε ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have hs0 : 0 < Real.sqrt (4 + ε ^ 2) := by linarith
  have hpre : 4 * reciprocalN ε * ε / reciprocalT ε ≤ 6 * ε := by
    apply (div_le_iff₀ hT).2
    have h1 := mul_nonneg (le_of_lt he) (sub_nonneg.mpr ht.2.1)
    have h2 := mul_nonneg (le_of_lt he) (sub_nonneg.mpr ht.2.2.1)
    nlinarith
  have hbr : 4 + (1 - 4 * ε) / Real.sqrt (4 + ε ^ 2) ≤ 9 / 2 := by
    have hdiv : (1 - 4 * ε) / Real.sqrt (4 + ε ^ 2) ≤ 1 / 2 := by
      apply (div_le_iff₀ hs0).2
      linarith
    linarith
  have hbr0 : 0 ≤ 4 + (1 - 4 * ε) / Real.sqrt (4 + ε ^ 2) := by
    have : 0 ≤ 1 - 4 * ε := by linarith
    positivity
  have h := mul_le_mul hpre hbr hbr0 (by positivity : 0 ≤ 6 * ε)
  dsimp [reciprocalMeanFormula]
  nlinarith

/-- Exact peak lower bound for the reciprocal return-loss ratio. -/
theorem reciprocalRatio_peak {ε c : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16)
    (hc : 0 ≤ c) (hc' : c ≤ ε ^ 2 / 4) :
    4 / 3 ≤ reciprocalRatio ε c := by
  have ht := reciprocal_trace_bounds he he'
  have hT : 0 < reciprocalT ε := by linarith [ht.2.2.1]
  have hN : 0 < reciprocalN ε := by linarith [ht.1]
  have hden : 0 < 4 * c + ε ^ 2 := by positivity
  have hfrac : 1 / (2 * ε) ≤ (16 * c + ε) / (4 * c + ε ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) hden).2
    have hprod : 0 ≤ ε * c := mul_nonneg (le_of_lt he) hc
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hfrac
    (by positivity : 0 ≤ 4 * reciprocalN ε * ε / reciprocalT ε)
  have he0 : ε ≠ 0 := ne_of_gt he
  have hvalue : (4 * reciprocalN ε * ε / reciprocalT ε) * (1 / (2 * ε)) =
      2 * reciprocalN ε / reciprocalT ε := by
    field_simp
    ring
  rw [hvalue] at hmul
  have hl : 4 / 3 ≤ 2 * reciprocalN ε / reciprocalT ε := by
    apply (le_div_iff₀ hT).2
    linarith [ht.1, ht.2.2.2]
  exact le_trans hl hmul

theorem reciprocalRatio_time_peak {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16)
    (ht : t ∈ Set.Icc (Real.pi - ε) (Real.pi + ε)) :
    4 / 3 ≤ reciprocalRatio ε (Real.cos (t / 2) ^ 2) :=
  reciprocalRatio_peak he he' (sq_nonneg _) (cos_half_peak (le_of_lt he) ht)

/-- Exact partial-fraction decomposition used for the main period integral. -/
theorem mainRatio_decomposition {ε c : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    (hc : 0 ≤ c) :
    mainRatio ε c = (17 * mainD ε / (45 * (1 - ε))) *
      (1 + ε * (1 - 2 * ε) / (4 * (1 - ε) ^ 2 * c + ε ^ 2)) := by
  have hden := mainRatio_denominator_pos he hc
  have hε1 : 1 - ε ≠ 0 := by linarith
  unfold mainRatio
  field_simp
  ring

/-- Exact partial-fraction decomposition used for the reciprocal period integral. -/
theorem reciprocalRatio_decomposition {ε c : ℝ} (he : 0 < ε) (hc : 0 ≤ c) :
    reciprocalRatio ε c = (4 * reciprocalN ε * ε / reciprocalT ε) *
      (4 + ε * (1 - 4 * ε) / (4 * c + ε ^ 2)) := by
  have hden : 4 * c + ε ^ 2 ≠ 0 := by positivity
  unfold reciprocalRatio
  field_simp
  ring

/-- Actual normalized period integral of the main return-loss ratio. -/
theorem main_period_mean {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
      mainRatio ε (Real.cos (t / 2) ^ 2)) = mainMeanFormula ε := by
  have ha : 0 < 4 * (1 - ε) ^ 2 := by
    have : 0 < 1 - ε := by linarith
    positivity
  have h := Krylov.mean_affine_inv_cos_half_sq ha (sq_pos_of_pos he)
    (17 * mainD ε / (45 * (1 - ε))) (ε * (1 - 2 * ε)) 1
  have hfun : (fun t : ℝ => mainRatio ε (Real.cos (t / 2) ^ 2)) =
      (fun t : ℝ => (17 * mainD ε / (45 * (1 - ε))) *
        (1 + ε * (1 - 2 * ε) / (4 * (1 - ε) ^ 2 * Real.cos (t / 2) ^ 2 + ε ^ 2))) := by
    funext t
    exact mainRatio_decomposition he he' (sq_nonneg _)
  rw [hfun, h]
  have hsqrt : Real.sqrt (ε ^ 2 * (4 * (1 - ε) ^ 2 + ε ^ 2)) =
      ε * Real.sqrt (4 * (1 - ε) ^ 2 + ε ^ 2) := by
    rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq (le_of_lt he)]
  rw [hsqrt]
  unfold mainMeanFormula
  congr 2
  exact mul_div_mul_left _ _ (ne_of_gt he)

/-- Actual normalized period integral of the reciprocal return-loss ratio. -/
theorem reciprocal_period_mean {ε : ℝ} (he : 0 < ε) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
      reciprocalRatio ε (Real.cos (t / 2) ^ 2)) = reciprocalMeanFormula ε := by
  have h := Krylov.mean_affine_inv_cos_half_sq (by norm_num : (0 : ℝ) < 4)
    (sq_pos_of_pos he) (4 * reciprocalN ε * ε / reciprocalT ε) (ε * (1 - 4 * ε)) 4
  have hfun : (fun t : ℝ => reciprocalRatio ε (Real.cos (t / 2) ^ 2)) =
      (fun t : ℝ => (4 * reciprocalN ε * ε / reciprocalT ε) *
        (4 + ε * (1 - 4 * ε) / (4 * Real.cos (t / 2) ^ 2 + ε ^ 2))) := by
    funext t
    exact reciprocalRatio_decomposition he (sq_nonneg _)
  rw [hfun, h]
  have hsqrt : Real.sqrt (ε ^ 2 * (4 + ε ^ 2)) = ε * Real.sqrt (4 + ε ^ 2) := by
    rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq (le_of_lt he)]
  rw [hsqrt]
  unfold reciprocalMeanFormula
  congr 2
  exact mul_div_mul_left _ _ (ne_of_gt he)

theorem main_period_mean_bound {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
      mainRatio ε (Real.cos (t / 2) ^ 2)) ≤ 68 / 81 := by
  rw [main_period_mean he he']
  exact mainMeanFormula_bound he he'

theorem reciprocal_period_mean_bound {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
      reciprocalRatio ε (Real.cos (t / 2) ^ 2)) ≤ 27 * ε := by
  rw [reciprocal_period_mean he]
  exact reciprocalMeanFormula_bound he he'

theorem mainRatio_continuous {ε : ℝ} (he : 0 < ε) :
    Continuous (fun t : ℝ => mainRatio ε (Real.cos (t / 2) ^ 2)) := by
  unfold mainRatio
  apply continuous_const.mul
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    exact ne_of_gt (mainRatio_denominator_pos he (sq_nonneg _))

theorem reciprocalRatio_continuous {ε : ℝ} (he : 0 < ε) :
    Continuous (fun t : ℝ => reciprocalRatio ε (Real.cos (t / 2) ^ 2)) := by
  unfold reciprocalRatio
  apply continuous_const.mul
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    positivity

theorem mainRatio_pos {ε c : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) (hc : 0 ≤ c) :
    0 < mainRatio ε c := by
  have hd : 0 < mainD ε := by linarith [(mainD_bounds he he').1]
  have he1 : 0 < 1 - ε := by linarith
  unfold mainRatio
  positivity

theorem reciprocalRatio_pos {ε c : ℝ} (he : 0 < ε) (hc : 0 ≤ c) :
    0 < reciprocalRatio ε c := by
  unfold reciprocalRatio reciprocalN reciprocalT
  positivity

theorem mainMeanFormula_pos {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    0 < mainMeanFormula ε := by
  have hd : 0 < mainD ε := by linarith [(mainD_bounds he he').1]
  have he1 : 0 < 1 - ε := by linarith
  have he2 : 0 ≤ 1 - 2 * ε := by linarith
  unfold mainMeanFormula
  positivity

theorem reciprocalMeanFormula_pos {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16) :
    0 < reciprocalMeanFormula ε := by
  have ht := reciprocal_trace_bounds he he'
  have hN : 0 < reciprocalN ε := by linarith [ht.1]
  have hT : 0 < reciprocalT ε := by linarith [ht.2.2.1]
  have he4 : 0 ≤ 1 - 4 * ε := by linarith
  unfold reciprocalMeanFormula
  positivity

theorem main_period_mean_pos {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    0 < (1 / (2 * Real.pi)) * (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
      mainRatio ε (Real.cos (t / 2) ^ 2)) := by
  rw [main_period_mean he he']
  exact mainMeanFormula_pos he he'

theorem reciprocal_period_mean_pos {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16) :
    0 < (1 / (2 * Real.pi)) * (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
      reciprocalRatio ε (Real.cos (t / 2) ^ 2)) := by
  rw [reciprocal_period_mean he]
  exact reciprocalMeanFormula_pos he he'

/-- Monotonicity of the actual recurrence-period average. -/
theorem periodMean_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t : ℝ, f t ≤ g t) : Temporal.periodMean f ≤ Temporal.periodMean g := by
  unfold Temporal.periodMean
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (fun t _ => hfg t)

theorem periodMean_const_mul (a : ℝ) (f : ℝ → ℝ) :
    Temporal.periodMean (fun t => a * f t) = a * Temporal.periodMean f := by
  unfold Temporal.periodMean
  rw [intervalIntegral.integral_const_mul]
  ring

theorem main_periodMean_eq {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    Temporal.periodMean (fun t => mainRatio ε (Real.cos (t / 2) ^ 2)) = mainMeanFormula ε := by
  unfold Temporal.periodMean
  convert main_period_mean he he' using 1
  ring

theorem reciprocal_periodMean_eq {ε : ℝ} (he : 0 < ε) :
    Temporal.periodMean (fun t => reciprocalRatio ε (Real.cos (t / 2) ^ 2)) =
      reciprocalMeanFormula ε := by
  unfold Temporal.periodMean
  convert reciprocal_period_mean he using 1
  ring

/-- Transfer of the main-family CV lower bound to any continuous ratio within
the proved return-loss envelope. The envelope is a hypothesis, not an assertion
that an arbitrary operator ratio has already been identified. -/
theorem main_cv_of_envelope {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4)
    {r : ℝ → ℝ} (hr : Continuous r)
    (hlower : ∀ t : ℝ, mainRatio ε (Real.cos (t / 2) ^ 2) / 8 ≤ r t)
    (hupper : ∀ t : ℝ, r t ≤ 8 * mainRatio ε (Real.cos (t / 2) ^ 2)) :
    289 / (132710400 * Real.pi * ε) - 1 ≤ Temporal.cvSquared r := by
  have hf := mainRatio_continuous he
  have hlow := periodMean_mono (continuous_const.mul hf) hr
    (fun t => show (1 / 8 : ℝ) * mainRatio ε (Real.cos (t / 2) ^ 2) ≤ r t by
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hlower t)
  rw [periodMean_const_mul, main_periodMean_eq he he'] at hlow
  have hμ : 0 < Temporal.periodMean r :=
    lt_of_lt_of_le (mul_pos (by norm_num) (mainMeanFormula_pos he he')) hlow
  have hupp := periodMean_mono hr (continuous_const.mul hf) hupper
  rw [periodMean_const_mul, main_periodMean_eq he he'] at hupp
  have hμupper : Temporal.periodMean r ≤ 8 := by
    linarith [mainMeanFormula_bound he he']
  apply Temporal.main_cv_of_peak_and_mean hr he (by linarith [Real.pi_gt_three]) hμ hμupper
  intro t ht
  have hpeak := mainRatio_time_peak he he' ht
  have hp := div_le_div_of_nonneg_right hpeak (by norm_num : (0 : ℝ) ≤ 8)
  have he0 : ε ≠ 0 := ne_of_gt he
  have heq : (17 / (180 * ε)) / 8 = 17 / (1440 * ε) := by ring
  rw [heq] at hp
  exact hp.trans (hlower t)

/-- Reciprocal-family CV lower bound for continuous ratios in its envelope. -/
theorem reciprocal_cv_of_envelope {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 16)
    {q : ℝ → ℝ} (hq : Continuous q)
    (hlower : ∀ t : ℝ, reciprocalRatio ε (Real.cos (t / 2) ^ 2) / 8 ≤ q t)
    (hupper : ∀ t : ℝ, q t ≤ 8 * reciprocalRatio ε (Real.cos (t / 2) ^ 2)) :
    1 / (1679616 * Real.pi * ε) - 1 ≤ Temporal.cvSquared q := by
  have hf := reciprocalRatio_continuous he
  have hlow := periodMean_mono (continuous_const.mul hf) hq
    (fun t => show (1 / 8 : ℝ) * reciprocalRatio ε (Real.cos (t / 2) ^ 2) ≤ q t by
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hlower t)
  rw [periodMean_const_mul, reciprocal_periodMean_eq he] at hlow
  have hμ : 0 < Temporal.periodMean q :=
    lt_of_lt_of_le (mul_pos (by norm_num) (reciprocalMeanFormula_pos he he')) hlow
  have hupp := periodMean_mono hq (continuous_const.mul hf) hupper
  rw [periodMean_const_mul, reciprocal_periodMean_eq he] at hupp
  have hμupper : Temporal.periodMean q ≤ 216 * ε := by
    linarith [reciprocalMeanFormula_bound he he']
  apply Temporal.reciprocal_cv_of_peak_and_mean hq he
    (by linarith [Real.pi_gt_three]) hμ hμupper
  intro t ht
  have hpeak := reciprocalRatio_time_peak he he' ht
  have hp := div_le_div_of_nonneg_right hpeak (by norm_num : (0 : ℝ) ≤ 8)
  norm_num at hp
  exact hp.trans (hlower t)

/-- General explicit small-parameter argument for quantified unboundedness. -/
theorem inverse_parameter_unbounded {K cap : ℝ} (hK : 0 < K) (hcap : 0 < cap)
    (F : ℝ → ℝ) (hF : ∀ ε : ℝ, 0 < ε → ε ≤ cap → K / ε - 1 ≤ F ε)
    (M : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ε ≤ cap ∧ M < F ε := by
  let ε : ℝ := min (cap / 2) (K / (|M| + 2))
  have hA : 0 < |M| + 2 := by positivity
  have he : 0 < ε := by
    dsimp [ε]
    exact lt_min (by positivity) (by positivity)
  have hecap : ε ≤ cap := by
    have h := min_le_left (cap / 2) (K / (|M| + 2))
    dsimp [ε]
    linarith
  have heK : ε ≤ K / (|M| + 2) := min_le_right _ _
  have hratio : |M| + 2 ≤ K / ε := by
    apply (le_div_iff₀ he).2
    have h := (le_div_iff₀ hA).1 heK
    nlinarith
  refine ⟨ε, he, hecap, ?_⟩
  have h := hF ε he hecap
  have hM := le_abs_self M
  linarith

/-- No finite CV-squared bound for any continuous family satisfying the main
return-loss comparison envelope at every positive parameter in its range. -/
theorem main_envelope_cv_unbounded (r : ℝ → ℝ → ℝ)
    (hr : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → Continuous (r ε))
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ t : ℝ,
      mainRatio ε (Real.cos (t / 2) ^ 2) / 8 ≤ r ε t)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ t : ℝ,
      r ε t ≤ 8 * mainRatio ε (Real.cos (t / 2) ^ 2)) (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ M < Temporal.cvSquared (r ε) := by
  apply inverse_parameter_unbounded
    (show 0 < (289 : ℝ) / (132710400 * Real.pi) by positivity)
    (by norm_num : (0 : ℝ) < 1 / 4) (fun ε => Temporal.cvSquared (r ε)) _ M
  intro ε he he'
  simpa only [div_div] using main_cv_of_envelope he he'
    (hr ε he he') (hlower ε he he') (hupper ε he he')

/-- No finite CV-squared bound for continuous reciprocal-envelope families. -/
theorem reciprocal_envelope_cv_unbounded (q : ℝ → ℝ → ℝ)
    (hq : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 → Continuous (q ε))
    (hlower : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 → ∀ t : ℝ,
      reciprocalRatio ε (Real.cos (t / 2) ^ 2) / 8 ≤ q ε t)
    (hupper : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 → ∀ t : ℝ,
      q ε t ≤ 8 * reciprocalRatio ε (Real.cos (t / 2) ^ 2)) (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 16 ∧ M < Temporal.cvSquared (q ε) := by
  apply inverse_parameter_unbounded
    (show 0 < (1 : ℝ) / (1679616 * Real.pi) by positivity)
    (by norm_num : (0 : ℝ) < 1 / 16) (fun ε => Temporal.cvSquared (q ε)) _ M
  intro ε he he'
  simpa only [div_div] using reciprocal_cv_of_envelope he he'
    (hq ε he he') (hlower ε he he') (hupper ε he he')

/-- The main return-loss ratio itself gives a completely specified continuous
family with unbounded CV-squared. No comparison-envelope hypothesis remains. -/
theorem main_return_loss_cv_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧
      M < Temporal.cvSquared (fun t => mainRatio ε (Real.cos (t / 2) ^ 2)) := by
  apply main_envelope_cv_unbounded (fun ε t => mainRatio ε (Real.cos (t / 2) ^ 2))
  · intro ε he _
    exact mainRatio_continuous he
  · intro ε he he' t
    have hp := mainRatio_pos he he' (sq_nonneg (Real.cos (t / 2)))
    linarith
  · intro ε he he' t
    have hp := mainRatio_pos he he' (sq_nonneg (Real.cos (t / 2)))
    linarith

/-- The reciprocal return-loss ratio itself also has unbounded CV-squared. -/
theorem reciprocal_return_loss_cv_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 16 ∧
      M < Temporal.cvSquared (fun t => reciprocalRatio ε (Real.cos (t / 2) ^ 2)) := by
  apply reciprocal_envelope_cv_unbounded
    (fun ε t => reciprocalRatio ε (Real.cos (t / 2) ^ 2))
  · intro ε he _
    exact reciprocalRatio_continuous he
  · intro ε he _ t
    have hp := reciprocalRatio_pos he (sq_nonneg (Real.cos (t / 2)))
    linarith
  · intro ε he _ t
    have hp := reciprocalRatio_pos he (sq_nonneg (Real.cos (t / 2)))
    linarith

end Krylov.TemporalFamilies
