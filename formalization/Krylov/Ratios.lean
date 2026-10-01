import Mathlib

/-!
# Scalar ratio certificates

This file proves the load-bearing scalar algebra in the fixed-purity family
and the unbounded qutrit family of the manuscript.  The passage from a density
matrix and its Lanczos chain to these scalar expressions is NOT assumed as an
axiom and is NOT asserted here: the conclusions apply to the displayed scalar
functions.  Matrix positivity, the spectral reduction, and period-integral
identities are separate obligations.
-/

noncomputable section

namespace Krylov.Ratios

/-- The reduced ratio in the manuscript's fixed-purity family, with
`x = sin(t/2)^2`. This expression includes its removable value at `x = 0`. -/
def fixedPurityRatio (ε x : ℝ) : ℝ :=
  (5 / (18 * ε)) *
    ((1 + (1 - ε / 5) * x) / (1 + (1 - 18 * ε ^ 2 / 25) * x))

private theorem fixedPurity_coefficients {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 5 / 18) :
    0 < 1 - 18 * ε ^ 2 / 25 ∧ 18 * ε ^ 2 / 25 ≤ ε / 5 := by
  have hprod : 0 < ε * (5 / 18 - ε) := mul_pos hε (sub_pos.mpr hε')
  constructor <;> nlinarith

/-- Positivity of the reduced denominator throughout the physical range. -/
theorem fixedPurity_denominator_pos {ε x : ℝ} (hε : 0 < ε)
    (hε' : ε < 5 / 18) (hx : 0 ≤ x) :
    0 < 1 + (1 - 18 * ε ^ 2 / 25) * x := by
  have hc := (fixedPurity_coefficients hε hε').1
  positivity

/-- Both uniform bounds from the fixed-purity theorem, for every real parameter
in the stated open interval and every `x ∈ [0,1]`. -/
theorem fixedPurity_bounds {ε x : ℝ} (hε : 0 < ε)
    (hε' : ε < 5 / 18) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    (5 / (18 * ε)) * (1 - ε / 10) ≤ fixedPurityRatio ε x ∧
      fixedPurityRatio ε x ≤ 5 / (18 * ε) := by
  have hd := fixedPurity_denominator_pos hε hε' hx
  have hp : 0 ≤ 5 / (18 * ε) := le_of_lt (by positivity)
  have hc := (fixedPurity_coefficients hε hε').2
  have hlow : 1 - ε / 10 ≤
      (1 + (1 - ε / 5) * x) / (1 + (1 - 18 * ε ^ 2 / 25) * x) := by
    apply (le_div_iff₀ hd).2
    have h1 : 0 ≤ (ε / 10) * (1 - x) := mul_nonneg (by positivity) (sub_nonneg.mpr hx')
    have h2 : 0 ≤ (18 * ε ^ 2 / 25) * (1 - ε / 10) * x := by
      have : 0 ≤ 1 - ε / 10 := by linarith
      positivity
    nlinarith
  have hupp : (1 + (1 - ε / 5) * x) /
      (1 + (1 - 18 * ε ^ 2 / 25) * x) ≤ 1 := by
    apply (div_le_iff₀ hd).2
    have := mul_nonneg (sub_nonneg.mpr hc) hx
    nlinarith
  constructor
  · exact mul_le_mul_of_nonneg_left hlow hp
  · simpa [fixedPurityRatio] using mul_le_mul_of_nonneg_left hupp hp

/-- A simpler lower bound that is convenient for exact unboundedness witnesses. -/
theorem fixedPurity_lower_simple {ε x : ℝ} (hε : 0 < ε)
    (hε' : ε < 5 / 18) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    1 / (4 * ε) ≤ fixedPurityRatio ε x := by
  apply le_trans _ (fixedPurity_bounds hε hε' hx hx').1
  apply (div_le_iff₀ (by positivity : 0 < 4 * ε)).2
  have he : ε ≠ 0 := ne_of_gt hε
  have hcalc : (5 / (18 * ε)) * (1 - ε / 10) * (4 * ε) = (10 - ε) / 9 := by
    field_simp
    ring
  rw [hcalc]
  linarith

/-- Quantified uniform divergence, with an explicit positive finite parameter.
It excludes any finite upper bound for this scalar family, even uniformly
across all time coordinates `x ∈ [0,1]`. -/
theorem fixedPurity_uniform_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 5 / 18 ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 → M < fixedPurityRatio ε x := by
  let ε : ℝ := 1 / (8 * (|M| + 1))
  have hA : 0 < |M| + 1 := by positivity
  have he : 0 < ε := by dsimp [ε]; positivity
  have he' : ε < 5 / 18 := by
    dsimp [ε]
    apply (div_lt_iff₀ (by positivity : 0 < 8 * (|M| + 1))).2
    have := abs_nonneg M
    nlinarith
  refine ⟨ε, he, he', ?_⟩
  intro x hx hx'
  apply lt_of_lt_of_le _ (fixedPurity_lower_simple he he' hx hx')
  have habs : M ≤ |M| := le_abs_self M
  have hEq : 1 / (4 * ε) = 2 * (|M| + 1) := by
    dsimp [ε]
    field_simp
    ring
  rw [hEq]
  linarith

/-- The three-atom complexity after replacing `sin(t/2)^2` by `x`. -/
def threeAtomComplexity (μ x : ℝ) : ℝ := 4 * μ * x * (1 + (1 - 2 * μ) * x)

/-- A general exact difference identity, independent of any matrix reduction. -/
theorem threeAtom_difference (a b x : ℝ) :
    threeAtomComplexity a x - threeAtomComplexity b x =
      (a - b) * (4 * x * (1 - x) + 8 * (1 - a - b) * x ^ 2) := by
  unfold threeAtomComplexity
  ring

/-- Strict order of the three-atom complexities away from recurrence (`x=0`). -/
theorem threeAtom_strict_order {a b x : ℝ} (hab : b < a)
    (hsum : a + b < 1) (hx : 0 < x) (hx' : x ≤ 1) :
    threeAtomComplexity b x < threeAtomComplexity a x := by
  have h1 : 0 ≤ 4 * x * (1 - x) := mul_nonneg (by positivity) (sub_nonneg.mpr hx')
  have h2 : 0 < 8 * (1 - a - b) * x ^ 2 := by
    have : 0 < 1 - a - b := by linarith
    positivity
  have hd := threeAtom_difference a b x
  have : 0 < (a - b) * (4 * x * (1 - x) + 8 * (1 - a - b) * x ^ 2) := by
    exact mul_pos (sub_pos.mpr hab) (by linarith)
  linarith

/-- The continued scalar ratio at a common recurrence. -/
theorem fixedPurity_at_recurrence (ε : ℝ) :
    fixedPurityRatio ε 0 = 5 / (18 * ε) := by
  simp [fixedPurityRatio]

/-- Exact algebraic reduction of the quotient of three-atom complexities.
The strict `x > 0` hypothesis excludes the common zero before cancellation. -/
theorem fixedPurity_spectral_quotient {ε x : ℝ} (hε : 0 < ε)
    (hε' : ε < 5 / 18) (hx : 0 < x) :
    threeAtomComplexity (ε / 10) x / threeAtomComplexity (9 * ε ^ 2 / 25) x =
      fixedPurityRatio ε x := by
  have he : ε ≠ 0 := ne_of_gt hε
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hd := fixedPurity_denominator_pos hε hε' (le_of_lt hx)
  have hd0 : 1 + (1 - 18 * ε ^ 2 / 25) * x ≠ 0 := ne_of_gt hd
  have hgeneral (A D : ℝ) (hD : D ≠ 0) :
      ((2 * ε * x / 5) * A) / ((36 * ε ^ 2 * x / 25) * D) =
        (5 / (18 * ε)) * (A / D) := by
    field_simp
    ring
  have hS : threeAtomComplexity (ε / 10) x =
      (2 * ε * x / 5) * (1 + (1 - ε / 5) * x) := by
    unfold threeAtomComplexity
    ring
  have hK : threeAtomComplexity (9 * ε ^ 2 / 25) x =
      (36 * ε ^ 2 * x / 25) * (1 + (1 - 18 * ε ^ 2 / 25) * x) := by
    unfold threeAtomComplexity
    ring
  rw [hS, hK]
  exact hgeneral _ _ hd0

/-- At fixed purity the reciprocal has an explicit uniform vanishing bound. -/
theorem fixedPurity_reciprocal_bounds {ε x : ℝ} (hε : 0 < ε)
    (hε' : ε < 5 / 18) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    0 < 1 / fixedPurityRatio ε x ∧ 1 / fixedPurityRatio ε x ≤ 4 * ε := by
  have hl := fixedPurity_lower_simple hε hε' hx hx'
  have hp : 0 < fixedPurityRatio ε x :=
    lt_of_lt_of_le (by positivity : 0 < 1 / (4 * ε)) hl
  constructor
  · positivity
  · apply (div_le_iff₀ hp).2
    have h := (div_le_iff₀ (by positivity : 0 < 4 * ε)).1 hl
    nlinarith

/-- Negated boundedness formulation of the fixed-purity scalar no-go result. -/
theorem fixedPurity_no_finite_upper :
    ¬ ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < 5 / 18 →
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 → fixedPurityRatio ε x ≤ M := by
  rintro ⟨M, hM⟩
  obtain ⟨ε, he, he', hr⟩ := fixedPurity_uniform_unbounded M
  exact (not_lt_of_ge (hM ε he he' 1 (by norm_num) (by norm_num)))
    (hr 1 (by norm_num) (by norm_num))

/-- Spectral weights in the qutrit family, parametrized by `z = m²`. -/
def qutritWeightS (z : ℝ) : ℝ := 1 / (2 * (z + 5))
def qutritWeightK (z : ℝ) : ℝ := 9 / (2 * (z ^ 2 + 17))

/-- The two positive weights are ordered and their sum is strictly below one.
This supplies all hypotheses needed for the all-time strict scalar comparison. -/
theorem qutrit_weights {z : ℝ} (hz : 16 ≤ z) :
    0 < qutritWeightK z ∧ qutritWeightK z < qutritWeightS z ∧
      qutritWeightS z + qutritWeightK z < 1 ∧ qutritWeightS z < 1 / 2 := by
  have hza : 0 < 2 * (z + 5) := by linarith
  have hzb : 0 < 2 * (z ^ 2 + 17) := by positivity
  have hz2 : 256 ≤ z ^ 2 := by nlinarith
  have hprod : 0 ≤ z * (z - 16) := mul_nonneg (by linarith) (by linarith)
  have ha : qutritWeightS z < 1 / 4 := by
    unfold qutritWeightS
    apply (div_lt_iff₀ hza).2
    linarith
  have hb : qutritWeightK z < 1 / 4 := by
    unfold qutritWeightK
    apply (div_lt_iff₀ hzb).2
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold qutritWeightK
    positivity
  · unfold qutritWeightK qutritWeightS
    apply (div_lt_div_iff₀ hzb hza).2
    nlinarith
  · linarith
  · linarith

/-- Scalar version of the qutrit all-time comparison: strict for every
nonrecurrence coordinate `0 < x ≤ 1`. -/
theorem qutrit_strict_order {z x : ℝ} (hz : 16 ≤ z)
    (hx : 0 < x) (hx' : x ≤ 1) :
    threeAtomComplexity (qutritWeightK z) x <
      threeAtomComplexity (qutritWeightS z) x := by
  have hw := qutrit_weights hz
  exact threeAtom_strict_order hw.2.1 hw.2.2.1 hx hx'

/-- Exact peak-time complexity ratio of the qutrit scalar family. -/
def qutritPeakRatio (z : ℝ) : ℝ :=
  (qutritWeightS z * (1 - qutritWeightS z)) /
    (qutritWeightK z * (1 - qutritWeightK z))

/-- A convenient explicit lower bound suffices to prove unboundedness. -/
theorem qutrit_peak_lower {z : ℝ} (hz : 16 ≤ z) :
    z / 36 ≤ qutritPeakRatio z := by
  have hw := qutrit_weights hz
  have ha := hw.2.2.2
  have hb0 := hw.1
  have hb1 : qutritWeightK z < 1 := by linarith [hw.2.1]
  have hd : 0 < qutritWeightK z * (1 - qutritWeightK z) := mul_pos hb0 (sub_pos.mpr hb1)
  have hza : 0 < 2 * (z + 5) := by linarith
  have hzb : 0 < 2 * (z ^ 2 + 17) := by positivity
  have hab : (z / 36) * qutritWeightK z ≤ qutritWeightS z / 2 := by
    unfold qutritWeightK qutritWeightS
    have hzpos : 0 ≤ z := by linarith
    have hprod := mul_nonneg hzpos (show 0 ≤ z - 5 by linarith)
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (le_div_iff₀ hza).2
    field_simp
    apply (div_le_iff₀ (by positivity : 0 < 36 * (2 * (z ^ 2 + 17)))).2
    nlinarith
  have hleft : (z / 36) * (qutritWeightK z * (1 - qutritWeightK z)) ≤
      (z / 36) * qutritWeightK z := by
    have := mul_nonneg (show 0 ≤ z / 36 by positivity) (sq_nonneg (qutritWeightK z))
    nlinarith
  have haright : qutritWeightS z / 2 ≤ qutritWeightS z * (1 - qutritWeightS z) := by
    have ha0 : 0 ≤ qutritWeightS z := by linarith [hw.2.1]
    have := mul_nonneg ha0 (show 0 ≤ 1 / 2 - qutritWeightS z by linarith)
    nlinarith
  unfold qutritPeakRatio
  exact (le_div_iff₀ hd).2 (le_trans hleft (le_trans hab haright))

/-- No finite upper bound for the qutrit scalar peak ratio, with `z = m²`.
The explicit witness is a finite real parameter, rather than a singular limit. -/
theorem qutrit_peak_unbounded (M : ℝ) :
    ∃ m : ℝ, 4 ≤ m ∧ M < qutritPeakRatio (m ^ 2) := by
  let m : ℝ := 6 * (|M| + 1) + 4
  have hm : 4 ≤ m := by dsimp [m]; have := abs_nonneg M; linarith
  have hm2 : 16 ≤ m ^ 2 := by nlinarith
  refine ⟨m, hm, lt_of_lt_of_le ?_ (qutrit_peak_lower hm2)⟩
  have habs : M ≤ |M| := le_abs_self M
  dsimp [m]
  nlinarith [sq_nonneg (|M|)]

/-- The normalized peak ratio expressed as a rational function of `1/z`. -/
theorem qutrit_peak_normalized {z : ℝ} (hz : 16 ≤ z) :
    qutritPeakRatio z / z =
      ((2 + 9 * z⁻¹) * (1 + 17 * (z⁻¹) ^ 2) ^ 2) /
        (9 * (1 + 5 * z⁻¹) ^ 2 * (2 + 25 * (z⁻¹) ^ 2)) := by
  have hz0 : 0 < z := by linarith
  have hzp : 0 < z + 5 := by linarith
  have hz2 : 0 < z ^ 2 + 17 := by positivity
  have hz3 : 0 < 2 * z ^ 2 + 25 := by positivity
  have hB : 2 * (z ^ 2 + 17) - 9 ≠ 0 := by nlinarith
  unfold qutritPeakRatio qutritWeightS qutritWeightK
  field_simp [hB]
  ring

/-- Exact asymptotic coefficient: the qutrit peak ratio divided by `z`
tends to `1/9` as `z` tends to infinity. -/
theorem qutrit_peak_asymptotic :
    Filter.Tendsto (fun z : ℝ => qutritPeakRatio z / z)
      Filter.atTop (nhds (1 / 9 : ℝ)) := by
  let f : ℝ → ℝ := fun u =>
    ((2 + 9 * u) * (1 + 17 * u ^ 2) ^ 2) /
      (9 * (1 + 5 * u) ^ 2 * (2 + 25 * u ^ 2))
  have hf : ContinuousAt f 0 := by
    dsimp [f]
    fun_prop (disch := norm_num)
  have ht := hf.tendsto.comp (tendsto_inv_atTop_zero :
    Filter.Tendsto (fun z : ℝ => z⁻¹) Filter.atTop (nhds 0))
  have hteq : f 0 = (1 / 9 : ℝ) := by norm_num [f]
  rw [hteq] at ht
  apply ht.congr'
  filter_upwards [Filter.eventually_ge_atTop (16 : ℝ)] with z hz
  exact (qutrit_peak_normalized hz).symm

/-- The manuscript's `m²/9` asymptotic for the scalar qutrit family. -/
theorem qutrit_peak_asymptotic_m :
    Filter.Tendsto (fun m : ℝ => qutritPeakRatio (m ^ 2) / (m ^ 2))
      Filter.atTop (nhds (1 / 9 : ℝ)) := by
  exact qutrit_peak_asymptotic.comp (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))

/-- The qutrit eigenvalue list is positive, has trace one, and has the claimed
purity. This is an eigenvalue-list certificate, not a matrix spectral theorem. -/
theorem qutrit_eigenvalue_certificate {z : ℝ} (hz : 16 ≤ z) :
    0 < z / (z + 5) ∧ 0 < 4 / (z + 5) ∧ 0 < 1 / (z + 5) ∧
      z / (z + 5) + 4 / (z + 5) + 1 / (z + 5) = 1 ∧
      (z / (z + 5)) ^ 2 + (4 / (z + 5)) ^ 2 + (1 / (z + 5)) ^ 2 =
        (z ^ 2 + 17) / (z + 5) ^ 2 := by
  have hzpos : 0 < z := by linarith
  have hd : z + 5 ≠ 0 := by linarith
  refine ⟨by positivity, by positivity, by positivity, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring

theorem threeAtom_at_one (μ : ℝ) :
    threeAtomComplexity μ 1 = 8 * (μ * (1 - μ)) := by
  unfold threeAtomComplexity
  ring

/-- Positivity ensures that division at the qutrit peak is legitimate. -/
theorem qutrit_peak_complexity_pos {z : ℝ} (hz : 16 ≤ z) :
    0 < threeAtomComplexity (qutritWeightK z) 1 := by
  have hw := qutrit_weights hz
  have hb : qutritWeightK z < 1 := by linarith [hw.2.1, hw.2.2.2]
  rw [threeAtom_at_one]
  exact mul_pos (by norm_num) (mul_pos hw.1 (sub_pos.mpr hb))

/-- The reduced peak ratio really is the quotient of the scalar complexities. -/
theorem qutrit_peak_ratio_eq (z : ℝ) :
    qutritPeakRatio z =
      threeAtomComplexity (qutritWeightS z) 1 /
        threeAtomComplexity (qutritWeightK z) 1 := by
  rw [threeAtom_at_one, threeAtom_at_one]
  unfold qutritPeakRatio
  rw [mul_div_mul_left _ _ (by norm_num : (8 : ℝ) ≠ 0)]

/-- Quantified no-go theorem for any fixed positive multiplier, conditional
only on the explicitly defined scalar three-atom representation. -/
theorem qutrit_no_positive_multiplier :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, 4 ≤ m →
      c * threeAtomComplexity (qutritWeightS (m ^ 2)) 1 ≤
        threeAtomComplexity (qutritWeightK (m ^ 2)) 1 := by
  rintro ⟨c, hc, hall⟩
  obtain ⟨m, hm, hratio⟩ := qutrit_peak_unbounded (1 / c)
  have hz : 16 ≤ m ^ 2 := by nlinarith
  have hpos := qutrit_peak_complexity_pos hz
  rw [qutrit_peak_ratio_eq] at hratio
  have hlt := (lt_div_iff₀ hpos).1 hratio
  have hscaled := mul_lt_mul_of_pos_left hlt hc
  have hcancel : c * ((1 / c) * threeAtomComplexity (qutritWeightK (m ^ 2)) 1) =
      threeAtomComplexity (qutritWeightK (m ^ 2)) 1 := by
    field_simp
  rw [hcancel] at hscaled
  exact (not_lt_of_ge (hall m hm)) hscaled

/-- Scalar radicand in the fixed-purity eigenvalue construction. -/
def fixedPurityDiscriminant (ε : ℝ) : ℝ := 2 * ε - 59 * ε ^ 2 / 25

def fixedPurityEigenPlus (ε : ℝ) : ℝ :=
  (1 - ε + Real.sqrt (fixedPurityDiscriminant ε)) / 2

def fixedPurityEigenMinus (ε : ℝ) : ℝ :=
  (1 - ε - Real.sqrt (fixedPurityDiscriminant ε)) / 2

/-- All four listed eigenvalues are positive, sum to one, and have squared sum
exactly `1/2` throughout the entire fixed-purity parameter interval. -/
theorem fixedPurity_eigenvalue_certificate {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 5 / 18) :
    0 < fixedPurityDiscriminant ε ∧
    0 < fixedPurityEigenPlus ε ∧ 0 < fixedPurityEigenMinus ε ∧
    0 < 4 * ε / 5 ∧ 0 < ε / 5 ∧
    fixedPurityEigenPlus ε + fixedPurityEigenMinus ε + 4 * ε / 5 + ε / 5 = 1 ∧
    (fixedPurityEigenPlus ε) ^ 2 + (fixedPurityEigenMinus ε) ^ 2 +
      (4 * ε / 5) ^ 2 + (ε / 5) ^ 2 = 1 / 2 := by
  have hr : 0 < fixedPurityDiscriminant ε := by
    unfold fixedPurityDiscriminant
    have hp : 0 < ε * (2 - 59 * ε / 25) := by
      apply mul_pos hε
      linarith
    nlinarith
  have hd : fixedPurityDiscriminant ε < (1 - ε) ^ 2 := by
    have hp : 0 < (1 - 14 * ε / 5) * (1 - 6 * ε / 5) := by
      apply mul_pos <;> linarith
    unfold fixedPurityDiscriminant
    nlinarith
  have hs : Real.sqrt (fixedPurityDiscriminant ε) < 1 - ε :=
    (Real.sqrt_lt' (by linarith : 0 < 1 - ε)).2 hd
  have hs0 := Real.sqrt_nonneg (fixedPurityDiscriminant ε)
  have hs2 := Real.sq_sqrt (le_of_lt hr)
  refine ⟨hr, ?_, ?_, by positivity, by positivity, ?_, ?_⟩
  · unfold fixedPurityEigenPlus
    linarith
  · unfold fixedPurityEigenMinus
    linarith
  · unfold fixedPurityEigenPlus fixedPurityEigenMinus
    ring
  · unfold fixedPurityEigenPlus fixedPurityEigenMinus
    unfold fixedPurityDiscriminant at hs2 ⊢
    nlinarith

end Krylov.Ratios
