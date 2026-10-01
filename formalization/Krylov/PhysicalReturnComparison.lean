import Krylov.ActualReturnBounds
import Krylov.PhysicalCurvatureNecessary

/-! The source return-comparison corollary for actual normalized GS chains,
canonical square roots, trace return amplitudes and actual cyclic dimensions. -/
namespace Krylov.PhysicalReturnComparison
open Matrix PerturbedDynamics TaylorRemainder ActualReturnBounds
open PhysicalCurvatureNecessary CanonicalPurification PurificationBranches
open scoped InnerProductSpace BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def spreadReturn (H : Matrix ι ι ℂ) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (t : ℝ) : ℝ :=
  (trace ((evolvedDensity_posSemidef H hρ t).sqrt * hρ.sqrt)).re

def mixedReturn (H ρ : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  (trace (evolvedDensity H ρ t * ρ)).re / purity ρ

def spreadLength (H : Matrix ι ι ℂ) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) : ℕ :=
  chainLength (liouvillian H) (FactorTwo.rowVectorize hρ.sqrt)

def mixedLength (H ρ : Matrix ι ι ℂ) : ℕ :=
  chainLength (liouvillian H) (normalizedSeed ρ)

lemma matrix_evolution_eq (H A : Matrix ι ι ℂ) (t : ℝ) :
    UnitaryCovariance.evolution H A t = evolvedDensity H A t := by
  rw [evolvedDensity_eq]
  simp [UnitaryCovariance.evolution,UnitaryEvolution.propagator,Complex.ofReal_neg,neg_mul]

lemma real_trace_cast (z : ℂ) (hz : z.im=0) : (z.re:ℂ)=z := by
  apply Complex.ext <;> simp [hz]

lemma spread_return_amplitude {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (t : ℝ) :
    ⟪FactorTwo.rowVectorize hρ.sqrt,
      evolution (skewGenerator (liouvillian H)) (FactorTwo.rowVectorize hρ.sqrt) t⟫_ℂ =
      (spreadReturn H hρ t : ℂ) := by
  rw [evolution_rowVectorize H _ hH,FactorTwo.rowVectorize_inner]
  change OperatorBridge.hsInner hρ.sqrt (UnitaryCovariance.evolution H hρ.sqrt t) = _
  rw [UnitaryCovariance.hsInner_eq_trace,hρ.posSemidef_sqrt.isHermitian.eq,
    matrix_evolution_eq,evolvedDensity_eq,evolved_sqrt hH hρ,trace_mul_comm]
  exact (real_trace_cast _ (Krylov.psd_overlap_real_nonnegative _ _
    (evolvedDensity_posSemidef H hρ t).posSemidef_sqrt hρ.posSemidef_sqrt).1).symm

lemma mixed_return_amplitude {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (t : ℝ) :
    ⟪normalizedSeed ρ,evolution (skewGenerator (liouvillian H)) (normalizedSeed ρ) t⟫_ℂ =
      (mixedReturn H ρ t : ℂ) := by
  have hscale (c : ℂ) :
      evolution (skewGenerator (liouvillian H)) (c • FactorTwo.rowVectorize ρ) t =
        c • evolution (skewGenerator (liouvillian H)) (FactorTwo.rowVectorize ρ) t := by
    exact map_smul _ c _
  have hz : (trace (evolvedDensity H ρ t * ρ)).im=0 :=
    (Krylov.psd_overlap_real_nonnegative _ _ (evolvedDensity_posSemidef H hρ t) hρ).1
  rw [normalizedSeed,hscale,inner_smul_left,inner_smul_right,evolution_rowVectorize H _ hH,
    FactorTwo.rowVectorize_inner]
  change star ((‖FactorTwo.rowVectorize ρ‖⁻¹:ℝ):ℂ) *
    (((‖FactorTwo.rowVectorize ρ‖⁻¹:ℝ):ℂ) * OperatorBridge.hsInner ρ
      (UnitaryCovariance.evolution H ρ t)) = _
  rw [UnitaryCovariance.hsInner_eq_trace,hρ.isHermitian.eq,matrix_evolution_eq,trace_mul_comm]
  rw [← real_trace_cast _ hz]
  simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,
    mixedReturn,← Complex.ofReal_div]
  apply congrArg Complex.ofReal
  rw [div_eq_mul_inv,← purity_norm hρ.isHermitian]
  simp only [inv_pow]
  ring

/-- The literal source trace returns lie in [0,1]. -/
theorem source_return_bounds {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : trace ρ=1) (t : ℝ) :
    spreadReturn H hρ t ∈ Set.Icc (0:ℝ) 1 ∧ mixedReturn H ρ t ∈ Set.Icc (0:ℝ) 1 := by
  have hs0 : 0 ≤ spreadReturn H hρ t := (Krylov.psd_overlap_real_nonnegative _ _
    (evolvedDensity_posSemidef H hρ t).posSemidef_sqrt hρ.posSemidef_sqrt).2
  have hk0 : 0 ≤ mixedReturn H ρ t := div_nonneg
    (Krylov.psd_overlap_real_nonnegative _ _ (evolvedDensity_posSemidef H hρ t) hρ).2
    (Krylov.density_trace_square_positive ρ hρ htr).le
  have hsn : ‖FactorTwo.rowVectorize hρ.sqrt‖=1 := seed_unit hρ htr
  have hkn := normalizedSeed_unit htr
  have hs := norm_inner_le_norm (𝕜 := ℂ) (FactorTwo.rowVectorize hρ.sqrt)
    (evolution (skewGenerator (liouvillian H)) (FactorTwo.rowVectorize hρ.sqrt) t)
  have hk := norm_inner_le_norm (𝕜 := ℂ) (normalizedSeed ρ)
    (evolution (skewGenerator (liouvillian H)) (normalizedSeed ρ) t)
  rw [spread_return_amplitude hH hρ,evolution_norm _ (liouvillian_selfAdjoint _ hH),hsn] at hs
  rw [mixed_return_amplitude hH hρ,evolution_norm _ (liouvillian_selfAdjoint _ hH),hkn] at hk
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs0,abs_of_nonneg hk0,one_mul] at hs hk
  exact ⟨⟨hs0,hs⟩,⟨hk0,hk⟩⟩

/-- Both actual finite-chain return inequalities, with source trace amplitudes
and true cyclic lengths. -/
theorem source_individual_bounds {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : trace ρ=1) (t : ℝ) :
    (1-spreadReturn H hρ t^2  ≤  spread (generatorU H) (seed hρ) t ∧
      spread (generatorU H) (seed hρ) t  ≤ 
        ((spreadLength H hρ:ℝ)-1)*(1-spreadReturn H hρ t^2)) ∧
    (1-mixedReturn H ρ t^2  ≤  PhysicalCurvatureNecessary.mixedComplexity H ρ t ∧
      PhysicalCurvatureNecessary.mixedComplexity H ρ t  ≤ 
        ((mixedLength H ρ:ℝ)-1)*(1-mixedReturn H ρ t^2)) := by
  have hs := actual_return_bounds (liouvillian H) (liouvillian_selfAdjoint _ hH)
    (FactorTwo.rowVectorize hρ.sqrt) (seed_unit hρ htr) t
  have hk := actual_return_bounds (liouvillian H) (liouvillian_selfAdjoint _ hH)
    (normalizedSeed ρ) (normalizedSeed_unit htr) t
  rw [spread_return_amplitude hH hρ] at hs
  rw [mixed_return_amplitude hH hρ] at hk
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs] at hs hk
  rw [spread_actual hH hρ]
  exact ⟨hs,hk⟩

/-- The positive-return factor-eight corollary for actual chains of at most
five nodes. This also discharges the generic physical form of source lem:return. -/
theorem source_loss_bounds {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : trace ρ=1) (t : ℝ) :
    (spreadLength H hρ ≤ 5 →
      1-spreadReturn H hρ t ≤ spread (generatorU H) (seed hρ) t ∧
      spread (generatorU H) (seed hρ) t ≤ 8*(1-spreadReturn H hρ t)) ∧
    (mixedLength H ρ ≤ 5 →
      1-mixedReturn H ρ t ≤ PhysicalCurvatureNecessary.mixedComplexity H ρ t ∧
      PhysicalCurvatureNecessary.mixedComplexity H ρ t ≤ 8*(1-mixedReturn H ρ t)) := by
  have scalar (A C M : ℝ) (hA : A ∈ Set.Icc (0:ℝ) 1) (hM : M ≤ 4)
      (hlo : 1-A^2 ≤ C) (hhi : C ≤ M*(1-A^2)) : 1-A ≤ C ∧ C ≤ 8*(1-A) := by
    have hs : 0 ≤ 1-A^2 := by nlinarith [hA.1,hA.2]
    have hm := mul_le_mul_of_nonneg_right hM hs
    have hprod := mul_nonneg hA.1 (sub_nonneg.mpr hA.2)
    constructor <;> nlinarith
  obtain ⟨hS,hK⟩ := source_return_bounds hH hρ htr t
  obtain ⟨hSb,hKb⟩ := source_individual_bounds hH hρ htr t
  constructor
  · intro hmS
    have hSm : (spreadLength H hρ:ℝ)-1 ≤ 4 := by
      have h : (spreadLength H hρ:ℝ) ≤ 5 := by exact_mod_cast hmS
      linarith
    exact scalar _ _ _ hS hSm hSb.1 hSb.2
  · intro hmK
    have hKm : (mixedLength H ρ:ℝ)-1 ≤ 4 := by
      have h : (mixedLength H ρ:ℝ) ≤ 5 := by exact_mod_cast hmK
      linarith
    exact scalar _ _ _ hK hKm hKb.1 hKb.2

/-- Source cor:return-comparison for every actual finite density flow. The only
extra time restrictions are the source's two nonzero return losses. -/
theorem physical_return_comparison {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : trace ρ=1) (t : ℝ)
    (hsne : spreadReturn H hρ t ≠ 1) (hkne : mixedReturn H ρ t ≠ 1) :
    (1-spreadReturn H hρ t^2)/(((mixedLength H ρ:ℝ)-1)*(1-mixedReturn H ρ t^2))  ≤ 
      spread (generatorU H) (seed hρ) t / PhysicalCurvatureNecessary.mixedComplexity H ρ t ∧
    spread (generatorU H) (seed hρ) t / PhysicalCurvatureNecessary.mixedComplexity H ρ t  ≤ 
      (((spreadLength H hρ:ℝ)-1)*(1-spreadReturn H hρ t^2))/(1-mixedReturn H ρ t^2) := by
  obtain ⟨hsb,hkb⟩ := source_return_bounds hH hρ htr t
  obtain ⟨⟨hSlo,hShi⟩,⟨hKlo,hKhi⟩⟩ := source_individual_bounds hH hρ htr t
  have hSL : 0<1-spreadReturn H hρ t^2 := by
    have hlt := lt_of_le_of_ne hsb.2 hsne
    nlinarith [hsb.1]
  have hKL : 0<1-mixedReturn H ρ t^2 := by
    have hlt := lt_of_le_of_ne hkb.2 hkne
    nlinarith [hkb.1]
  have hKpos : 0<PhysicalCurvatureNecessary.mixedComplexity H ρ t := hKL.trans_le hKlo
  have hSupper0 : 0 ≤ ((spreadLength H hρ:ℝ)-1)*(1-spreadReturn H hρ t^2) :=
    (hSL.le.trans hSlo).trans hShi
  constructor
  · exact (div_le_div_of_nonneg_left hSL.le hKpos hKhi).trans
      (div_le_div_of_nonneg_right hSlo hKpos.le)
  · exact (div_le_div_of_nonneg_right hShi hKpos.le).trans
      (div_le_div_of_nonneg_left hSupper0 hKL hKlo)

/-- The spread length is also literally the cardinality of the normalized
state GS chain for the source's doubled-space U* generator. -/
theorem spread_length_literal {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) :
    spreadLength H hρ = Fintype.card
      (FactorTwoFinite.GSIndex (FactorTwoFinite.stateSequence (generatorU H) (seed hρ))) := by
  have he : powerSequence (liouvillian H) (FactorTwo.rowVectorize hρ.sqrt) =
      FactorTwoFinite.stateSequence (generatorU H) (seed hρ) := by
    funext n
    rw [generatorU_eq_commutatorMatrix hH]
    exact PureShortTime.state_power (commutatorMatrix H) (seed hρ) n
  unfold spreadLength chainLength
  rw [he]

/-- The lengths in the comparison are exactly the dimensions of the actual
root and mixed-seed cyclic spaces. -/
theorem source_lengths {H ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    spreadLength H hρ = Module.finrank ℂ
      (FactorTwoFinite.cyclicSpan (powerSequence (liouvillian H) (FactorTwo.rowVectorize hρ.sqrt))) ∧
    mixedLength H ρ = Module.finrank ℂ
      (FactorTwoFinite.cyclicSpan (powerSequence (liouvillian H) (normalizedSeed ρ))) :=
  ⟨length_eq_cyclic_finrank _ _,length_eq_cyclic_finrank _ _⟩
end
end Krylov.PhysicalReturnComparison
