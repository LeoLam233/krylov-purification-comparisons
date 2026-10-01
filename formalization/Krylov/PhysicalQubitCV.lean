import Krylov.UniversalQubit
import Krylov.RestrictedCV

/-! Restricted coefficient-of-variation bounds for actual qubit matrices.
The source parameters are derived from the canonical positive root; no
Bloch-angle or independent scalar parameterization is assumed. -/
namespace Krylov.PhysicalQubitCV
open Matrix OperatorBridge PhysicalQubit UniversalQubit RestrictedCV
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 2000000

/-- Twice the determinant of the canonical positive square root. -/
def rootParameter {ρ : QubitMatrix} (hρ : ρ.PosSemidef) : ℝ := 2*hρ.sqrt.det.re

theorem hermitian_det_im_zero {A : QubitMatrix} (hA : A.IsHermitian) : A.det.im=0 := by
  rw [hA.det_eq_prod_eigenvalues]
  simp [Fin.prod_univ_succ, Complex.mul_im]

theorem purity_det_identity {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    purity ρ = 1-2*ρ.det.re := by
  have ht := diagonal_sum htr
  have ht2 := congrArg (fun x : ℝ => x^2) ht
  rw [purity_expansion hρ.isHermitian, hermitian_det hρ.isHermitian]
  nlinarith

theorem density_det_root {ρ : QubitMatrix} (hρ : ρ.PosSemidef) :
    ρ.det.re = hρ.sqrt.det.re ^ 2 := by
  have hd := congrArg Matrix.det hρ.sqrt_mul_self
  rw [Matrix.det_mul] at hd
  have hdi := hermitian_det_im_zero hρ.posSemidef_sqrt.isHermitian
  have hr := congrArg Complex.re hd
  simpa [Complex.mul_re, hdi, pow_two] using hr.symm

theorem purity_parameter {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    purity ρ = (2-rootParameter hρ^2)/2 := by
  rw [purity_det_identity hρ htr, density_det_root hρ, rootParameter]
  ring

theorem parameter_nonnegative {ρ : QubitMatrix} (hρ : ρ.PosSemidef) : 0 ≤ rootParameter hρ :=
  mul_nonneg (by norm_num) (psd_determinant_nonnegative hρ.posSemidef_sqrt)

theorem root_sum_parameter {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    ((hρ.sqrt 0 0).re+(hρ.sqrt 1 1).re)^2 = 1+rootParameter hρ := by
  have hn := sqrt_seed_normalized hρ htr
  rw [purity_expansion hρ.posSemidef_sqrt.isHermitian] at hn
  rw [rootParameter, hermitian_det hρ.posSemidef_sqrt.isHermitian]
  nlinarith

theorem root_difference_parameter {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    ((hρ.sqrt 0 0).re-(hρ.sqrt 1 1).re)^2+4*coherence hρ.sqrt = 1-rootParameter hρ := by
  have hn := sqrt_seed_normalized hρ htr
  rw [purity_expansion hρ.posSemidef_sqrt.isHermitian] at hn
  rw [rootParameter, hermitian_det hρ.posSemidef_sqrt.isHermitian]
  nlinarith

theorem coherence_parameter {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    coherence ρ = (1+rootParameter hρ)*coherence hρ.sqrt := by
  have hc := square_coherence hρ.posSemidef_sqrt.isHermitian
  rw [hρ.sqrt_mul_self, root_sum_parameter hρ htr] at hc
  exact hc

/-- Every nonstationary qubit's actual coefficients admit the exact source
parameterization, derived from its canonical root. -/
theorem physical_parameterization {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hS : 0<spreadCoefficient ρ hρ) :
    ∃ y h : ℝ, 0≤y ∧ y<1 ∧ 0<h ∧ h≤1 ∧
      spreadCoefficient ρ hρ=(1-y)*h/2 ∧
      mixedCoefficient ρ=(1-y^2)*h/(2-y^2) := by
  let y := rootParameter hρ
  let h := 4*coherence hρ.sqrt/(1-y)
  have hy : 0≤y := parameter_nonnegative hρ
  have hq : 0<coherence hρ.sqrt := by unfold spreadCoefficient at hS; linarith
  have hd := root_difference_parameter hρ htr
  have hy1 : y<1 := by
    dsimp [y]
    nlinarith [sq_nonneg ((hρ.sqrt 0 0).re-(hρ.sqrt 1 1).re)]
  have hden : 0<1-y := sub_pos.mpr hy1
  have hh : 0<h := div_pos (mul_pos (by norm_num) hq) hden
  have hh1 : h≤1 := by
    apply (div_le_iff₀ hden).2
    dsimp [y] at *
    nlinarith [sq_nonneg ((hρ.sqrt 0 0).re-(hρ.sqrt 1 1).re)]
  refine ⟨y,h,hy,hy1,hh,hh1,?_,?_⟩
  · dsimp [h,spreadCoefficient]
    field_simp
    ring
  · rw [mixedCoefficient, coherence_parameter hρ htr, purity_parameter hρ htr]
    dsimp [h,y]
    have hd1 : 1-rootParameter hρ ≠ 0 := hden.ne'
    have hd2 : 2-rootParameter hρ^2 ≠ 0 := by
      have hy' : 0≤rootParameter hρ := hy
      have hy1' : rootParameter hρ<1 := hy1
      nlinarith
    field_simp
    ring

/-- The physical all-time range factor is bounded by the exact universal
qubit constant. -/
theorem physical_range_factor {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hS : 0<spreadCoefficient ρ hρ) :
    (1-spreadCoefficient ρ hρ)/(1-mixedCoefficient ρ) ≤ kappaStar := by
  obtain ⟨y,h,hy,hy1,hh,hh1,ha,hb⟩ := physical_parameterization hρ htr hS
  rw [ha,hb]
  exact qubit_range_factor_bound hy hy1 hh.le hh1

open MeasureTheory

/-- Exact physical nonstationarity: nonzero energy gap and nonzero spread
spectral mass in that energy basis. -/
def Nonstationary {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) : Prop :=
  energyGap hH ≠ 0 ∧
    0 < spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ)

/-- The removable extension of the actual spread/mixed ratio. -/
def extendedRatio {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (t : ℝ) : ℝ :=
  continuedRatio (spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ))
    (mixedCoefficient (coordinateDensity hH ρ)) (Real.sin (energyGap hH*t/2)^2)

/-- The removable extension of the reciprocal physical ratio. -/
def extendedReciprocal {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (t : ℝ) : ℝ :=
  1 / extendedRatio hH hρ t

/-- The source normalization R=Pq uses the actual state's purity. -/
def extendedPurityRatio {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (t : ℝ) : ℝ :=
  purity ρ * extendedReciprocal hH hρ t

theorem threeAtom_quotient {a b t : ℝ} (hb : b ≠ 0) (hb' : b ≤ 1/2)
    (ht : Real.sin (t/2) ≠ 0) :
    Qubit.threeAtom a t / Qubit.threeAtom b t =
      continuedRatio a b (Real.sin (t/2)^2) := by
  have hd : 0<1+(1-2*b)*Real.sin (t/2)^2 := by
    have hh := mul_nonneg (show 0≤1-2*b by linarith) (sq_nonneg (Real.sin (t/2)))
    linarith
  rw [Qubit.threeAtom_polynomial, Qubit.threeAtom_polynomial]
  unfold continuedRatio
  field_simp
  ring

/-- The continued expression agrees with the actual ratio wherever the
physical denominator is nonzero, including arbitrary Hermitian H. -/
theorem ratio_eq_actual {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) {t : ℝ}
    (ht : Real.sin (energyGap hH*t/2) ≠ 0) :
    extendedRatio hH hρ t = spread hH hρ t / mixed hH ρ t := by
  obtain ⟨hs,hsk,hki,hi⟩ := coefficient_hierarchy (coordinateDensity_posSemidef hH hρ)
    (coordinateDensity_trace hH htr)
  rw [spread_eq hH hρ htr, mixed_eq hH hρ htr]
  exact (threeAtom_quotient (ne_of_gt (hn.2.trans_le hsk)) (hki.trans hi) ht).symm

theorem reciprocal_eq_actual {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) {t : ℝ}
    (ht : Real.sin (energyGap hH*t/2) ≠ 0) :
    extendedReciprocal hH hρ t = mixed hH ρ t / spread hH hρ t := by
  rw [extendedReciprocal, ratio_eq_actual hH hρ htr hn ht]
  simp

theorem extendedRatio_range {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) (t : ℝ) :
    extendedRatio hH hρ t ∈ Set.Icc
      (spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ) /
        mixedCoefficient (coordinateDensity hH ρ))
      ((spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ) /
        mixedCoefficient (coordinateDensity hH ρ))*kappaStar) := by
  obtain ⟨hs,hsk,hki,hi⟩ := coefficient_hierarchy (coordinateDensity_posSemidef hH hρ)
    (coordinateDensity_trace hH htr)
  exact continuedRatio_range hn.2 hsk (hki.trans hi) (sq_nonneg _) (Real.sin_sq_le_one _)
    (physical_range_factor (coordinateDensity_posSemidef hH hρ) (coordinateDensity_trace hH htr) hn.2)

theorem continuous_extendedRatio {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) : Continuous (extendedRatio hH hρ) := by
  obtain ⟨hs,hsk,hki,hi⟩ := coefficient_hierarchy (coordinateDensity_posSemidef hH hρ)
    (coordinateDensity_trace hH htr)
  have hd (t : ℝ) : 1+(1-2*mixedCoefficient (coordinateDensity hH ρ))*Real.sin (energyGap hH*t/2)^2 ≠ 0 := by
    have hh := mul_nonneg (show 0≤1-2*mixedCoefficient (coordinateDensity hH ρ) by linarith)
      (sq_nonneg (Real.sin (energyGap hH*t/2)))
    linarith
  unfold extendedRatio continuedRatio
  apply Continuous.mul continuous_const
  exact Continuous.div (by fun_prop) (by fun_prop) hd

/-- All three actual qubit ratios, continuously extended at recurrence
points, satisfy the bound under every probability-weighted time average. -/
theorem physical_qubit_cv {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    coefficientVariation (extendedRatio hH hρ) ν ≤ (kappaStar-1)/(2*Real.sqrt kappaStar) ∧
    coefficientVariation (extendedReciprocal hH hρ) ν ≤ (kappaStar-1)/(2*Real.sqrt kappaStar) ∧
    coefficientVariation (extendedPurityRatio hH hρ) ν ≤ (kappaStar-1)/(2*Real.sqrt kappaStar) := by
  obtain ⟨hs,hsk,hki,hi⟩ := coefficient_hierarchy (coordinateDensity_posSemidef hH hρ)
    (coordinateDensity_trace hH htr)
  have hm : 0 < spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ) /
      mixedCoefficient (coordinateDensity hH ρ) := div_pos hn.2 (hn.2.trans_le hsk)
  have hmeas : AEMeasurable (extendedRatio hH hρ) ν :=
    (continuous_extendedRatio hH hρ htr).aemeasurable
  have hr := Filter.Eventually.of_forall (f := ae ν) (extendedRatio_range hH hρ htr hn)
  have hrec := reciprocal_cv_of_range_factor ν hm kappaStar_gt_one.le hmeas hr
  refine ⟨cv_of_range_factor ν hm kappaStar_gt_one.le hmeas hr, hrec, ?_⟩
  have hp : 0 < purity ρ := by have := (purity_bounds hρ htr).1; linarith
  rw [show extendedPurityRatio hH hρ = fun t => purity ρ * extendedReciprocal hH hρ t from rfl,
    coefficientVariation_scale _ _ hp]
  exact hrec

/-- Physical nonstationarity is established directly by a nonzero original
matrix commutator, not imposed as a scalar parameterization. -/
theorem nonstationary_of_commutator_ne {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hc : matrixCommutator H ρ ≠ 0) :
    Nonstationary hH hρ := by
  have hcert := mixed_chain_certificate hH hρ htr
  have hstation : mixedCoefficient (coordinateDensity hH ρ)=0 ∨ energyGap hH=0 →
      matrixCommutator H ρ=0 := by
    intro hh
    have heff : (if energyGap hH=0 then 0 else mixedCoefficient (coordinateDensity hH ρ))=0 := by
      rcases hh with hh | hh <;> simp [hh]
    rw [heff] at hcert
    have hv := hcert.zero_mass_padding.1
    have hl := hcert.step_zero
    rw [hcert.seed, hv, smul_zero] at hl
    exact hl
  constructor
  · intro hg
    exact hc (hstation (Or.inr hg))
  · by_contra hn
    have hs := (coefficient_hierarchy (coordinateDensity_posSemidef hH hρ)
      (coordinateDensity_trace hH htr)).1
    have hz : spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ)=0 :=
      le_antisymm (le_of_not_gt hn) hs
    have hq : coherence (coordinateDensity_posSemidef hH hρ).sqrt=0 := by
      unfold spreadCoefficient at hz
      linarith
    have hqr := coherence_parameter (coordinateDensity_posSemidef hH hρ) (coordinateDensity_trace hH htr)
    rw [hq, mul_zero] at hqr
    apply hc
    apply hstation
    exact Or.inl (by simp [mixedCoefficient, hqr])

theorem commutator_ne_of_nonstationary {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hn : Nonstationary hH hρ) :
    matrixCommutator H ρ ≠ 0 := by
  intro hc
  have hcert := mixed_chain_certificate hH hρ htr
  simp only [if_neg hn.1] at hcert
  have hl := hcert.step_zero
  rw [hcert.seed, hc] at hl
  have hv : mixedChain hH ρ 1 = 0 :=
    (smul_eq_zero.mp hl.symm).resolve_left (Complex.ofReal_ne_zero.mpr hn.1)
  have hg := hcert.gram 1 1
  simp [hv, hsInner, ThreeAtomOperator.norms] at hg
  have hsk := (coefficient_hierarchy (coordinateDensity_posSemidef hH hρ)
    (coordinateDensity_trace hH htr)).2.1
  have hp : 0 < purity (coordinateDensity hH ρ) := hcert.scale_pos
  have hk : 0 < mixedCoefficient (coordinateDensity hH ρ) := hn.2.trans_le hsk
  exact hg.elim hp.ne' hk.ne'

theorem nonstationary_iff_commutator_ne {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    Nonstationary hH hρ ↔ matrixCommutator H ρ ≠ 0 :=
  ⟨commutator_ne_of_nonstationary hH hρ htr, nonstationary_of_commutator_ne hH hρ htr⟩

theorem extendedRatio_positive {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hn : Nonstationary hH hρ) (t : ℝ) :
    0 < extendedRatio hH hρ t := by
  have hsk := (coefficient_hierarchy (coordinateDensity_posSemidef hH hρ)
    (coordinateDensity_trace hH htr)).2.1
  exact (div_pos hn.2 (hn.2.trans_le hsk)).trans_le (extendedRatio_range hH hρ htr hn t).1

theorem continuous_extendedReciprocal {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hn : Nonstationary hH hρ) :
    Continuous (extendedReciprocal hH hρ) :=
  Continuous.div continuous_const (continuous_extendedRatio hH hρ htr)
    (fun t => (extendedRatio_positive hH hρ htr hn t).ne')

theorem continuous_extendedPurityRatio {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hn : Nonstationary hH hρ) :
    Continuous (extendedPurityRatio hH hρ) :=
  continuous_const.mul (continuous_extendedReciprocal hH hρ htr hn)

/-- Original physical version with nonstationarity stated solely as
[H,ρ]≠0, and no assumptions on any derived scalar coefficients. -/
theorem physical_qubit_cv_of_commutator_ne {H ρ : QubitMatrix}
    (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (hc : H*ρ-ρ*H ≠ 0) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    coefficientVariation (extendedRatio hH hρ) ν ≤ (kappaStar-1)/(2*Real.sqrt kappaStar) ∧
    coefficientVariation (extendedReciprocal hH hρ) ν ≤ (kappaStar-1)/(2*Real.sqrt kappaStar) ∧
    coefficientVariation (extendedPurityRatio hH hρ) ν ≤ (kappaStar-1)/(2*Real.sqrt kappaStar) :=
  physical_qubit_cv hH hρ htr (nonstationary_of_commutator_ne hH hρ htr hc) ν

theorem purityRatio_eq_actual {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hn : Nonstationary hH hρ) {t : ℝ}
    (ht : Real.sin (energyGap hH*t/2) ≠ 0) :
    extendedPurityRatio hH hρ t = purity ρ * (mixed hH ρ t / spread hH hρ t) := by
  rw [extendedPurityRatio, reciprocal_eq_actual hH hρ htr hn ht]

/-- Exact removable values, whose continuity is established above. -/
theorem recurrence_ratio_value {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) {t : ℝ} (ht : Real.sin (energyGap hH*t/2)=0) :
    extendedRatio hH hρ t =
      spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ) /
        mixedCoefficient (coordinateDensity hH ρ) := by
  simp [extendedRatio, continuedRatio, ht]

end
end Krylov.PhysicalQubitCV
