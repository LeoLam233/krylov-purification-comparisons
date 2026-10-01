import Krylov.PhysicalQubitCV

/-! The qubit ratio enclosure is attained at explicit times. The resulting
supremum/infimum quotient is the exact source range factor. -/
namespace Krylov.QubitRange
open Matrix PhysicalQubit UniversalQubit PhysicalQubitCV RestrictedCV
open scoped ComplexOrder
noncomputable section
set_option maxHeartbeats 400000

lemma continuedRatio_zero (a b : ℝ) : continuedRatio a b 0 = a/b := by
  simp [continuedRatio]

lemma continuedRatio_one (a b : ℝ) :
    continuedRatio a b 1 = (a/b)*((1-a)/(1-b)) := by
  unfold continuedRatio
  rw [show 1+(1-2*a)*1=2*(1-a) by ring,
    show 1+(1-2*b)*1=2*(1-b) by ring]
  rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]

/-- The maximizing scalar parameter belongs to the source's admissible interval. -/
theorem optimizing_parameter_admissible :
    (Real.sqrt 7-1)/3 ∈ Set.Ico (0:ℝ) 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7)
  have hn := Real.sqrt_nonneg 7
  constructor <;> nlinarith

/-- Exact attainment of the scalar range-polynomial bound. This is not an
attainment statement for the coefficient-of-variation bound. -/
theorem rangePolynomial_at_optimizer :
    rangePolynomial ((Real.sqrt 7-1)/3) = kappaStar := by
  have h := range_gap_factorization ((Real.sqrt 7-1)/3)
  simp only [sub_self,zero_pow (by decide : 2 ≠ 0),zero_mul,zero_div] at h
  exact (sub_eq_zero.mp h).symm

theorem rangePolynomial_maximum :
    IsGreatest (rangePolynomial '' Set.Ico (0:ℝ) 1) kappaStar := by
  refine ⟨⟨(Real.sqrt 7-1)/3,optimizing_parameter_admissible,rangePolynomial_at_optimizer⟩,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  exact rangePolynomial_le_kappaStar hy.1

def rangeFactor {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) : ℝ :=
  (1-spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ)) /
    (1-mixedCoefficient (coordinateDensity hH ρ))

lemma ratio_zero {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) :
    extendedRatio hH hρ 0 =
      spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ) /
        mixedCoefficient (coordinateDensity hH ρ) := by
  simp [extendedRatio,continuedRatio]

lemma half_period_phase {H : QubitMatrix} (hH : H.IsHermitian) (hgap : energyGap hH ≠ 0) :
    energyGap hH*(Real.pi/energyGap hH)/2 = Real.pi/2 := by
  field_simp [hgap]

lemma ratio_half_period {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (hgap : energyGap hH ≠ 0) :
    extendedRatio hH hρ (Real.pi/energyGap hH) =
      extendedRatio hH hρ 0 * rangeFactor hH hρ := by
  unfold extendedRatio
  rw [half_period_phase hH hgap,Real.sin_pi_div_two]
  simp only [one_pow,mul_zero,zero_div,Real.sin_zero,zero_pow (by decide : 2 ≠ 0),
    continuedRatio_zero,continuedRatio_one]
  rfl

/-- The upper endpoint occurs away from recurrence and is the actual
spread/mixed complexity quotient. The zero-time value above is its removable extension. -/
theorem half_period_ratio_eq_actual {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hn : Nonstationary hH hρ) :
    extendedRatio hH hρ (Real.pi/energyGap hH) =
      spread hH hρ (Real.pi/energyGap hH) / mixed hH ρ (Real.pi/energyGap hH) := by
  apply ratio_eq_actual hH hρ htr hn
  rw [half_period_phase hH hn.1,Real.sin_pi_div_two]
  norm_num

/-- Exact endpoint bounds, with no universal-constant relaxation. -/
theorem endpoint_bounds {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) (t : ℝ) :
    extendedRatio hH hρ 0 ≤ extendedRatio hH hρ t ∧
      extendedRatio hH hρ t ≤ extendedRatio hH hρ (Real.pi/energyGap hH) := by
  obtain ⟨hs,hsk,hki,hi⟩ := coefficient_hierarchy (coordinateDensity_posSemidef hH hρ)
    (coordinateDensity_trace hH htr)
  have h := continuedRatio_range hn.2 hsk (hki.trans hi)
    (sq_nonneg (Real.sin (energyGap hH*t/2))) (Real.sin_sq_le_one _)
    (le_refl (rangeFactor hH hρ))
  rw [ratio_half_period hH hρ hn.1,ratio_zero hH hρ]
  exact h

/-- The lower and upper endpoints are actual attained global extrema of the
continued physical ratio. -/
theorem ratio_extrema {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) :
    IsLeast (Set.range (extendedRatio hH hρ)) (extendedRatio hH hρ 0) ∧
    IsGreatest (Set.range (extendedRatio hH hρ))
      (extendedRatio hH hρ (Real.pi/energyGap hH)) := by
  constructor
  · refine ⟨⟨0,rfl⟩,?_⟩
    rintro _ ⟨t,rfl⟩
    exact (endpoint_bounds hH hρ htr hn t).1
  · refine ⟨⟨Real.pi/energyGap hH,rfl⟩,?_⟩
    rintro _ ⟨t,rfl⟩
    exact (endpoint_bounds hH hρ htr hn t).2

/-- Literal source `max r / min r = (1-μS)/(1-μK)`, with both extrema
attained and the minimum strictly positive. -/
theorem exact_range_factor {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) :
    sSup (Set.range (extendedRatio hH hρ)) /
      sInf (Set.range (extendedRatio hH hρ)) = rangeFactor hH hρ := by
  obtain ⟨hmin,hmax⟩ := ratio_extrema hH hρ htr hn
  rw [hmax.csSup_eq,hmin.csInf_eq,ratio_half_period hH hρ hn.1]
  exact mul_div_cancel_left₀ _ (extendedRatio_positive hH hρ htr hn 0).ne'

/-- Reciprocal extrema occur at the reversed endpoint times. -/
theorem reciprocal_extrema {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) :
    IsLeast (Set.range (extendedReciprocal hH hρ))
      (extendedReciprocal hH hρ (Real.pi/energyGap hH)) ∧
    IsGreatest (Set.range (extendedReciprocal hH hρ)) (extendedReciprocal hH hρ 0) := by
  constructor
  · refine ⟨⟨Real.pi/energyGap hH,rfl⟩,?_⟩
    rintro _ ⟨t,rfl⟩
    exact one_div_le_one_div_of_le (extendedRatio_positive hH hρ htr hn t)
      (endpoint_bounds hH hρ htr hn t).2
  · refine ⟨⟨0,rfl⟩,?_⟩
    rintro _ ⟨t,rfl⟩
    exact one_div_le_one_div_of_le (extendedRatio_positive hH hρ htr hn 0)
      (endpoint_bounds hH hρ htr hn t).1

theorem reciprocal_range_factor {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) :
    sSup (Set.range (extendedReciprocal hH hρ)) /
      sInf (Set.range (extendedReciprocal hH hρ)) = rangeFactor hH hρ := by
  obtain ⟨hmin,hmax⟩ := reciprocal_extrema hH hρ htr hn
  rw [hmax.csSup_eq,hmin.csInf_eq]
  unfold extendedReciprocal
  simp only [one_div,inv_div_inv]
  rw [ratio_half_period hH hρ hn.1]
  exact mul_div_cancel_left₀ _ (extendedRatio_positive hH hρ htr hn 0).ne'

/-- Positive purity rescaling preserves the same attained endpoint range. -/
theorem purityRatio_extrema {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) :
    IsLeast (Set.range (extendedPurityRatio hH hρ))
      (extendedPurityRatio hH hρ (Real.pi/energyGap hH)) ∧
    IsGreatest (Set.range (extendedPurityRatio hH hρ)) (extendedPurityRatio hH hρ 0) := by
  have hp : 0 ≤ purity ρ := le_trans (by norm_num : (0:ℝ) ≤ 1/2) (purity_bounds hρ htr).1
  obtain ⟨hmin,hmax⟩ := reciprocal_extrema hH hρ htr hn
  constructor
  · refine ⟨⟨Real.pi/energyGap hH,rfl⟩,?_⟩
    rintro _ ⟨t,rfl⟩
    exact mul_le_mul_of_nonneg_left (hmin.2 ⟨t,rfl⟩) hp
  · refine ⟨⟨0,rfl⟩,?_⟩
    rintro _ ⟨t,rfl⟩
    exact mul_le_mul_of_nonneg_left (hmax.2 ⟨t,rfl⟩) hp

theorem purityRatio_range_factor {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) :
    sSup (Set.range (extendedPurityRatio hH hρ)) /
      sInf (Set.range (extendedPurityRatio hH hρ)) = rangeFactor hH hρ := by
  have hp : 0 < purity ρ := by have := (purity_bounds hρ htr).1; linarith
  obtain ⟨hmin,hmax⟩ := purityRatio_extrema hH hρ htr hn
  rw [hmax.csSup_eq,hmin.csInf_eq]
  unfold extendedPurityRatio
  rw [mul_div_mul_left _ _ hp.ne']
  obtain ⟨hmin',hmax'⟩ := reciprocal_extrema hH hρ htr hn
  rw [← hmax'.csSup_eq,← hmin'.csInf_eq]
  exact reciprocal_range_factor hH hρ htr hn

/-- The original physical hypothesis supplies the nonzero frequency gap
and positivity internally; no independent scalar nonstationarity is assumed. -/
theorem all_range_factors_of_commutator_ne {H ρ : QubitMatrix}
    (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hc : H*ρ-ρ*H ≠ 0) :
    sSup (Set.range (extendedRatio hH hρ)) / sInf (Set.range (extendedRatio hH hρ)) =
      rangeFactor hH hρ ∧
    sSup (Set.range (extendedReciprocal hH hρ)) / sInf (Set.range (extendedReciprocal hH hρ)) =
      rangeFactor hH hρ ∧
    sSup (Set.range (extendedPurityRatio hH hρ)) / sInf (Set.range (extendedPurityRatio hH hρ)) =
      rangeFactor hH hρ := by
  have hn := nonstationary_of_commutator_ne hH hρ htr hc
  exact ⟨exact_range_factor hH hρ htr hn,reciprocal_range_factor hH hρ htr hn,
    purityRatio_range_factor hH hρ htr hn⟩
end
end Krylov.QubitRange
