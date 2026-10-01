import Krylov.CurvatureNecessary
import Krylov.PureShortTime
import Krylov.CanonicalPurification

namespace Krylov.PhysicalCurvatureNecessary
open Matrix PerturbedDynamics PurificationBranches PureShortTime UnitaryCovariance
open scoped InnerProductSpace ComplexOrder
noncomputable section
set_option maxHeartbeats 3000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hsNormSq (A : Matrix ι ι ℂ) : ℝ := ‖FactorTwo.rowVectorize A‖^2

def purity (ρ : Matrix ι ι ℂ) : ℝ := (trace (ρ*ρ)).re

def energyVariance (ρ H : Matrix ι ι ℂ) : ℝ :=
  (trace (ρ*(H*H))).re-(trace (ρ*H)).re^2

def normalizedSeed (A : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι×ι) :=
  ((‖FactorTwo.rowVectorize A‖⁻¹ : ℝ) : ℂ) • FactorTwo.rowVectorize A

def mixedComplexity (H ρ : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  actualComplexity (liouvillian H) (normalizedSeed ρ) t

lemma norm_ne_zero_of_trace_one {ρ : Matrix ι ι ℂ} (htr : trace ρ=1) :
    ‖FactorTwo.rowVectorize ρ‖ ≠ 0 := by
  intro hz
  have hρ : ρ=0 := FactorTwo.rowVectorize.injective (by simpa using norm_eq_zero.mp hz)
  simp [hρ] at htr

lemma normalizedSeed_unit {ρ : Matrix ι ι ℂ} (htr : trace ρ=1) :
    ‖normalizedSeed ρ‖=1 := by
  simp [normalizedSeed,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_of_trace_one htr)]

lemma normalizedSeed_orthogonal (H : Matrix ι ι ℂ) {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    ⟪normalizedSeed ρ,liouvillian H (normalizedSeed ρ)⟫_ℂ=0 := by
  simp [normalizedSeed,map_smul,inner_smul_left,inner_smul_right,
    seed_commutator_orthogonal H ρ hρ]

lemma purity_norm {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    ‖FactorTwo.rowVectorize ρ‖^2=purity ρ := by
  rw [@norm_sq_eq_re_inner ℂ,FactorTwo.rowVectorize_inner]
  change (OperatorBridge.hsInner ρ ρ).re=purity ρ
  rw [hsInner_eq_trace,hρ.eq]
  rfl


lemma normalizedSeed_eq_purity_seed {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    normalizedSeed ρ = FactorTwo.rowVectorize
      (((Real.sqrt (purity ρ))⁻¹ : ℝ) • ρ) := by
  have hn : Real.sqrt (purity ρ)=‖FactorTwo.rowVectorize ρ‖ := by
    rw [← purity_norm hρ,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  ext ij
  simp [normalizedSeed,hn,FactorTwo.rowVectorize]

lemma mixed_curvature (H : Matrix ι ι ℂ) {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    ‖liouvillian H (normalizedSeed ρ)‖^2=hsNormSq (H*ρ-ρ*H)/purity ρ := by
  rw [normalizedSeed,map_smul,norm_smul,mul_pow,liouvillian_rowVectorize]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_pow]
  rw [purity_norm hρ]
  simp [hsNormSq,div_eq_mul_inv,mul_comm]

lemma mean_real {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian) (hρ : ρ.IsHermitian) :
    ‖trace (ρ*H)‖^2=(trace (ρ*H)).re^2 := by
  have hs : star (trace (ρ*H))=trace (ρ*H) := by
    rw [← trace_conjTranspose,conjTranspose_mul,hH.eq,hρ.eq,trace_mul_comm]
  have him := congrArg Complex.im hs
  have hz : (trace (ρ*H)).im=0 := by
    simp only [Complex.star_def,Complex.conj_im] at him
    linarith
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,hz]
  ring

lemma branchI_variance {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) :
    stateVariance (generatorI H) (seed hρ)=energyVariance ρ H := by
  let S := hρ.sqrt
  have hS : Sᴴ=S := hρ.posSemidef_sqrt.isHermitian.eq
  have hSS : S*S=ρ := hρ.sqrt_mul_self
  have hm : ⟪FactorTwo.rowVectorize S,FactorTwo.rowVectorize (H*S)⟫_ℂ=trace (ρ*H) := by
    rw [FactorTwo.rowVectorize_inner]
    change OperatorBridge.hsInner S (H*S)=_
    rw [hsInner_eq_trace,hS,trace_mul_cycle',← mul_assoc,hSS]
  have hn : ‖FactorTwo.rowVectorize (H*S)‖^2=(trace (ρ*(H*H))).re := by
    rw [@norm_sq_eq_re_inner ℂ,FactorTwo.rowVectorize_inner]
    change (OperatorBridge.hsInner (H*S) (H*S)).re=_
    rw [hsInner_eq_trace,conjTranspose_mul,hS,hH.eq]
    congr 1
    calc
      trace (S*H*(H*S))=trace (S*(H*H)*S) := by congr 1; simp [mul_assoc]
      _=trace (S*S*(H*H)) := trace_mul_cycle _ _ _
      _=trace (ρ*(H*H)) := by rw [hSS]
  change ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι×ι)) (generatorI H) (FactorTwo.rowVectorize S)‖^2 -
    ‖⟪FactorTwo.rowVectorize S,(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι×ι))
      (generatorI H) (FactorTwo.rowVectorize S)⟫_ℂ‖^2=energyVariance ρ H
  rw [CanonicalPurification.generatorI_row,hn,hm,mean_real hH hρ.isHermitian]
  rfl

lemma spread_actual {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (t : ℝ) :
    spread (generatorU H) (seed hρ) t = actualComplexity (liouvillian H) (FactorTwo.rowVectorize hρ.sqrt) t := by
  rw [spread,← stateComplexity_physical,CanonicalPurification.generatorU_eq_commutatorMatrix hH]
  rfl

/-- Source eq:curvature-necessary, in its literal density/root/energy-variance
form. The sole comparison assumption is the source's all-time hierarchy itself;
normalization, regularity and quadratic expansion are all derived internally. -/
theorem hierarchy_forces_curvature {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : trace ρ=1)
    (hh : ∀ t : ℝ, spread (generatorU H) (seed hρ) t ≤ mixedComplexity H ρ t ∧
      mixedComplexity H ρ t ≤ pureOperator (generatorI H) (seed hρ) t) :
    hsNormSq (H*hρ.sqrt-hρ.sqrt*H) ≤ hsNormSq (H*ρ-ρ*H)/purity ρ ∧
      hsNormSq (H*ρ-ρ*H)/purity ρ ≤ 2*energyVariance ρ H := by
  have hsunit : ‖FactorTwo.rowVectorize hρ.sqrt‖=1 := seed_unit hρ htr
  have hpunit := pureVector_unit (seed hρ) (seed_unit hρ htr)
  have hl := CurvatureNecessary.curvature_le_of_all_time_le (liouvillian H) (liouvillian H)
    (liouvillian_selfAdjoint H hH) (liouvillian_selfAdjoint H hH)
    (FactorTwo.rowVectorize hρ.sqrt) (normalizedSeed ρ) hsunit (normalizedSeed_unit htr)
    (seed_commutator_orthogonal H _ hρ.posSemidef_sqrt.isHermitian)
    (normalizedSeed_orthogonal H hρ.isHermitian) (fun t => by
      simpa [spread_actual hH hρ t,mixedComplexity] using (hh t).1)
  have hr := CurvatureNecessary.curvature_le_of_all_time_le (liouvillian H)
    (liouvillian (generatorI H)) (liouvillian_selfAdjoint H hH)
    (liouvillian_selfAdjoint _ (generatorI_hermitian hH))
    (normalizedSeed ρ) (FactorTwo.rowVectorize (FactorTwo.pureSeed (seed hρ)))
    (normalizedSeed_unit htr) hpunit (normalizedSeed_orthogonal H hρ.isHermitian)
    (seed_commutator_orthogonal _ _ (pureSeed_hermitian _)) (fun t => by
      simpa [mixedComplexity,pureOperator,operatorComplexity_physical _ (generatorI_hermitian hH)] using (hh t).2)
  rw [liouvillian_rowVectorize,mixed_curvature H hρ.isHermitian] at hl
  rw [mixed_curvature H hρ.isHermitian,pure_commutator_norm _ (generatorI_hermitian hH)
    _ (seed_unit hρ htr),branchI_variance hH hρ] at hr
  exact ⟨hl,hr⟩
end
end Krylov.PhysicalCurvatureNecessary
