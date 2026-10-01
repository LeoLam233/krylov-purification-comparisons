import Mathlib

/-! Exact range-factor optimization and bounded-variable coefficient-of-variation
bound, for arbitrary probability-weighted averages. Physical qubit-ratio
identification is kept separate from this measure-theoretic theorem. -/
namespace Krylov.RestrictedCV
open MeasureTheory ProbabilityTheory
noncomputable section

def kappaStar : ℝ := (17+7*Real.sqrt 7)/27

def rangePolynomial (y : ℝ) : ℝ := (1+y)*(2-y^2)/2

theorem range_gap_factorization (y : ℝ) :
    kappaStar-rangePolynomial y =
      (y-(Real.sqrt 7-1)/3)^2 * (y+2*(Real.sqrt 7-1)/3+1)/2 := by
  have h : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  unfold kappaStar rangePolynomial
  ring_nf
  have h3 : Real.sqrt 7 ^ 3 = 7 * Real.sqrt 7 := by
    calc
      _ = Real.sqrt 7 ^ 2 * Real.sqrt 7 := by ring
      _ = _ := by rw [h]
  rw [h,h3]
  ring

theorem rangePolynomial_le_kappaStar {y : ℝ} (hy : 0 ≤ y) :
    rangePolynomial y ≤ kappaStar := by
  have h := Real.sqrt_nonneg 7
  have hf : 0 ≤ y+2*(Real.sqrt 7-1)/3+1 := by linarith
  have hp := mul_nonneg (sq_nonneg (y-(Real.sqrt 7-1)/3)) hf
  rw [← sub_nonneg]
  rw [range_gap_factorization]
  positivity

theorem kappaStar_gt_one : 1 < kappaStar := by
  have h : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 7
  unfold kappaStar
  nlinarith

/-- The polynomial source range factor dominates the full h-dependent range. -/
theorem qubit_range_factor_bound {y h : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (_hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (1-(1-y)*h/2)/(1-(1-y^2)*h/(2-y^2)) ≤ kappaStar := by
  have hd : 0 < 2-y^2 := by nlinarith
  have hb : 0 < 1-(1-y^2)*h/(2-y^2) := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hd).2
    nlinarith [mul_nonneg (show 0 ≤ 1-y^2 by nlinarith) (show 0 ≤ 1-h by linarith)]
  apply le_trans _ (rangePolynomial_le_kappaStar hy0)
  apply (div_le_iff₀ hb).2
  have he : rangePolynomial y * (1-(1-y^2)*h/(2-y^2)) -
      (1-(1-y)*h/2) = y*(1-h)*(1-y)*(y+2)/2 := by
    unfold rangePolynomial
    field_simp [ne_of_gt hd]
    ring
  have hys : 0 ≤ 1-y := sub_nonneg.mpr hy1.le
  have hhs : 0 ≤ 1-h := sub_nonneg.mpr hh1
  have hp : 0 ≤ y*(1-h)*(1-y)*(y+2)/2 := by positivity
  linarith


/-- The elementary optimization step behind the relative-variance bound. -/
theorem relative_variance_bound {m M u v : ℝ} (hm : 0 < m) (hM : m ≤ M)
    (hu : 0 < u) (hv : v ≤ (M-u)*(u-m)) :
    v/u^2 ≤ (M-m)^2/(4*m*M) := by
  have hMp : 0 < M := hm.trans_le hM
  apply (div_le_div_iff₀ (sq_pos_of_pos hu) (by positivity)).2
  have hmul := mul_le_mul_of_nonneg_right hv (show 0 ≤ 4*m*M by positivity)
  have hs := sq_nonneg ((M+m)*u-2*m*M)
  nlinarith

def coefficientVariation {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) : ℝ := Real.sqrt (variance X μ) / (∫ ω, X ω ∂μ)

theorem bounded_cv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {m M : ℝ}
    (hm : 0 < m) (hM : m ≤ M) (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc m M) :
    coefficientVariation X μ ≤ (M-m)/(2*Real.sqrt (m*M)) := by
  have hInt : Integrable X μ := (memLp_of_bounded h hX.aestronglyMeasurable 2).integrable
    (by norm_num)
  have hmean : m ≤ ∫ ω, X ω ∂μ := by
    have hi := integral_mono_ae (integrable_const m) hInt (h.mono fun ω hw => hw.1)
    simpa using hi
  have hmeanPos : 0 < ∫ ω, X ω ∂μ := hm.trans_le hmean
  have hv := variance_le_sub_mul_sub h hX
  have hrel := relative_variance_bound hm hM hmeanPos hv
  have hMp : 0 < M := hm.trans_le hM
  have hsM : Real.sqrt (m*M)^2 = m*M := Real.sq_sqrt (by positivity)
  have hsV : Real.sqrt (variance X μ)^2 = variance X μ := Real.sq_sqrt (variance_nonneg X μ)
  have hsqrt : 0 < Real.sqrt (m*M) := Real.sqrt_pos.2 (by positivity)
  unfold coefficientVariation
  apply (div_le_div_iff₀ hmeanPos (by positivity)).2
  have ha := (div_le_div_iff₀ (sq_pos_of_pos hmeanPos) (by positivity)).1 hrel
  have hleft : 0 ≤ Real.sqrt (variance X μ) * (2*Real.sqrt (m*M)) := by positivity
  have hright : 0 ≤ (M-m)*(∫ ω, X ω ∂μ) :=
    mul_nonneg (sub_nonneg.mpr hM) hmeanPos.le
  have hcompare : (Real.sqrt (variance X μ) * (2*Real.sqrt (m*M)))^2 ≤
      ((M-m)*(∫ ω, X ω ∂μ))^2 := by
    simp only [mul_pow, hsM, hsV]
    nlinarith
  nlinarith

theorem coefficientVariation_scale {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) {a : ℝ} (ha : 0 < a) :
    coefficientVariation (fun ω => a * X ω) μ = coefficientVariation X μ := by
  unfold coefficientVariation
  rw [variance_mul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
    abs_of_pos ha, integral_const_mul]
  exact mul_div_mul_left _ _ ha.ne'

theorem cv_of_range_factor {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {m κ : ℝ}
    (hm : 0 < m) (hκ : 1 ≤ κ) (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc m (m*κ)) :
    coefficientVariation X μ ≤ (κ-1)/(2*Real.sqrt κ) := by
  have hY : AEMeasurable (fun ω => (1/m)*X ω) μ := hX.const_mul _
  have hr : ∀ᵐ ω ∂μ, (1/m)*X ω ∈ Set.Icc 1 κ := by
    filter_upwards [h] with ω hw
    constructor
    · have hh := mul_le_mul_of_nonneg_left hw.1 (show 0 ≤ 1/m by positivity)
      field_simp at hh ⊢
      exact hh
    · have hh := mul_le_mul_of_nonneg_left hw.2 (show 0 ≤ 1/m by positivity)
      simpa [hm.ne', mul_assoc] using hh
  have hc := bounded_cv μ (m:=1) (M:=κ) (by norm_num) hκ hY hr
  rw [coefficientVariation_scale X μ (by positivity)] at hc
  simpa using hc

def continuedRatio (a b x : ℝ) : ℝ :=
  (a/b) * ((1+(1-2*a)*x)/(1+(1-2*b)*x))

theorem continuedRatio_range {a b x κ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1/2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hk : (1-a)/(1-b) ≤ κ) :
    continuedRatio a b x ∈ Set.Icc (a/b) ((a/b)*κ) := by
  have hbp : 0 < b := ha.trans_le hab
  have hd : 0 < 1+(1-2*b)*x := by nlinarith [mul_nonneg (show 0 ≤ 1-2*b by linarith) hx0]
  have h1b : 0 < 1-b := by linarith
  have hfac0 : (1:ℝ) ≤ (1+(1-2*a)*x)/(1+(1-2*b)*x) := by
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) hx0]
  have hfac1 : (1+(1-2*a)*x)/(1+(1-2*b)*x) ≤ (1-a)/(1-b) := by
    apply (div_le_div_iff₀ hd h1b).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hx1)]
  constructor
  · unfold continuedRatio
    have hh := mul_le_mul_of_nonneg_left hfac0 (show 0 ≤ a/b by positivity)
    simpa using hh
  · unfold continuedRatio
    exact mul_le_mul_of_nonneg_left (hfac1.trans hk) (by positivity)

/-- Uniform qubit CV bound once the three scalar coefficients are identified.
It holds for every probability measure and every measurable time-parameter
x in [0,1], including arbitrary weights on removable recurrence points. -/
theorem qubit_ratio_cv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1/2)
    (hk : (1-a)/(1-b) ≤ kappaStar) {x : Ω → ℝ}
    (hx : AEMeasurable x μ) (hr : ∀ᵐ ω ∂μ, x ω ∈ Set.Icc 0 1) :
    coefficientVariation (fun ω => continuedRatio a b (x ω)) μ ≤
      (kappaStar-1)/(2*Real.sqrt kappaStar) := by
  have hm : 0 < a/b := div_pos ha (ha.trans_le hab)
  apply cv_of_range_factor μ hm kappaStar_gt_one.le
  · unfold continuedRatio
    fun_prop
  · filter_upwards [hr] with ω hw
    exact continuedRatio_range ha hab hb hw.1 hw.2 hk


theorem qubit_coefficients {y h : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hh0 : 0 < h) (hh1 : h ≤ 1) :
    0 < (1-y)*h/2 ∧
    (1-y)*h/2 ≤ (1-y^2)*h/(2-y^2) ∧
    (1-y^2)*h/(2-y^2) ≤ 1/2 := by
  have hd : 0 < 2-y^2 := by nlinarith
  have hypos : 0 < 1-y := by linarith
  have hypl : 0 < y+2 := by linarith
  have hp : 0 ≤ y*(1-y)*h*(y+2) := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · apply (le_div_iff₀ hd).2
    nlinarith
  · apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg (show 0 ≤ 1-y^2 by nlinarith) (sub_nonneg.mpr hh1)]

theorem scalar_qubit_cv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {y h : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hh0 : 0 < h) (hh1 : h ≤ 1) {x : Ω → ℝ}
    (hx : AEMeasurable x μ) (hr : ∀ᵐ ω ∂μ, x ω ∈ Set.Icc 0 1) :
    coefficientVariation (fun ω =>
      continuedRatio ((1-y)*h/2) ((1-y^2)*h/(2-y^2)) (x ω)) μ ≤
      (kappaStar-1)/(2*Real.sqrt kappaStar) := by
  obtain ⟨ha,hab,hb⟩ := qubit_coefficients hy0 hy1 hh0 hh1
  exact qubit_ratio_cv μ ha hab hb
    (qubit_range_factor_bound hy0 hy1 hh0.le hh1) hx hr

theorem reciprocal_cv_of_range_factor {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {m κ : ℝ}
    (hm : 0 < m) (hκ : 1 ≤ κ) (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc m (m*κ)) :
    coefficientVariation (fun ω => 1/X ω) μ ≤ (κ-1)/(2*Real.sqrt κ) := by
  have hkp : 0 < κ := by linarith
  apply cv_of_range_factor μ (m:=1/(m*κ)) (by positivity) hκ (by simpa [one_div] using hX.inv)
  filter_upwards [h] with ω hw
  have hXp : 0 < X ω := hm.trans_le hw.1
  constructor
  · exact one_div_le_one_div_of_le hXp hw.2
  · have hi := one_div_le_one_div_of_le hm hw.1
    have he : (1/(m*κ))*κ = 1/m := by field_simp; ring
    rw [he]
    exact hi

end
end Krylov.RestrictedCV
