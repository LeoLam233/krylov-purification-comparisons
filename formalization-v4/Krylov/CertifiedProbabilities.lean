import Krylov.CertifiedMatrixGS
import Krylov.GSUnitaryTransport

namespace Krylov.CertifiedProbabilities
open Matrix OperatorBridge PhysicalCurvatureNecessary MatrixGSBridge
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Raw GS identity underlying both probability and Lanczos-norm tables. -/
theorem actual_raw_gram {d : ℕ} (H A : Operator ι)
    (v : Fin d → Operator ι) (p : Fin d → Polynomial ℂ)
    (hp : ∀ i, v i = (Polynomial.aeval (FactorTwo.commutator H)) (p i) A)
    (hd : ∀ i, (p i).degree = (i.val : WithBot ℕ))
    (ho : Pairwise (fun i j => hsInner (v i) (v j)=0)) (i : Fin d) :
    gramSchmidt ℂ
      (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H) (normalizedSeed A))
      i.val = (p i).leadingCoeff⁻¹ •
        (((‖FactorTwo.rowVectorize A‖⁻¹ : ℝ) : ℂ) • FactorTwo.rowVectorize (v i)) := by
  let Φ := polynomialMap H A
  have hc (j : Fin d) : (p j).leadingCoeff ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro hz
    have h := hd j
    simp [hz] at h
  have hv (j : Fin d) : Φ (p j) =
      ((‖FactorTwo.rowVectorize A‖⁻¹ : ℝ) : ℂ) • FactorTwo.rowVectorize (v j) := by
    rw [hp j]; rfl
  have hg : Pairwise (fun i j => ⟪Φ (p i),Φ (p j)⟫_ℂ=0) := by
    intro i j hij
    rw [hv,hv,inner_smul_left,inner_smul_right,FactorTwo.rowVectorize_inner]
    change _ * (_ * hsInner (v i) (v j)) = 0
    rw [ho hij]
    simp
  have h := CertifiedGS.gramSchmidt_eq_inv_smul
    (fun n => Φ (Polynomial.X^n)) (fun j => Φ (p j))
    (fun j => (p j).leadingCoeff) hc
    (fun j => CertifiedGS.polynomial_triangular Φ (p j) j.val (hd j)) hg i
  have hf : (fun n => Φ (Polynomial.X^n)) =
      PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H) (normalizedSeed A) :=
    funext (polynomialMap_power H A)
  rw [hf,hv] at h
  exact h

theorem monic_raw_norm {d : ℕ} (H A : Operator ι)
    (v : Fin d → Operator ι) (p : Fin d → Polynomial ℂ)
    (hp : ∀ i, v i = (Polynomial.aeval (FactorTwo.commutator H)) (p i) A)
    (hd : ∀ i, (p i).degree = (i.val : WithBot ℕ))
    (ho : Pairwise (fun i j => hsInner (v i) (v j)=0))
    (hm : ∀ i, (p i).Monic) (i : Fin d) :
    ‖gramSchmidt ℂ
      (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H) (normalizedSeed A))
      i.val‖^2 = (hsInner (v i) (v i)).re/(hsInner A A).re := by
  rw [actual_raw_gram H A v p hp hd ho i,(hm i),inv_one,one_smul,norm_smul,mul_pow]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_pow]
  rw [row_norm_sq A,row_norm_sq (v i)]
  ring

theorem monic_normed_gram {d : ℕ} (H A : Operator ι) (hA : A ≠ 0)
    (v : Fin d → Operator ι) (p : Fin d → Polynomial ℂ)
    (hp : ∀ i, v i = (Polynomial.aeval (FactorTwo.commutator H)) (p i) A)
    (hd : ∀ i, (p i).degree = (i.val : WithBot ℕ))
    (ho : Pairwise (fun i j => hsInner (v i) (v j)=0))
    (hm : ∀ i, (p i).Monic) (i : Fin d) :
    gramSchmidtNormed ℂ
      (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H) (normalizedSeed A))
      i.val = normalizedSeed (v i) := by
  have hn : ‖FactorTwo.rowVectorize A‖ ≠ 0 := by
    intro hz
    apply hA
    exact FactorTwo.rowVectorize.injective (by simpa using norm_eq_zero.mp hz)
  rw [gramSchmidtNormed,actual_raw_gram H A v p hp hd ho i,(hm i),inv_one,one_smul]
  have hh := CertifiedGS.normalize_smul_phase
    ((‖FactorTwo.rowVectorize A‖⁻¹ : ℝ) : ℂ) (FactorTwo.rowVectorize (v i))
  simp only [Complex.ofReal_inv] at hh
  simp only [Complex.ofReal_inv]
  refine hh.trans ?_
  simp [normalizedSeed,Complex.norm_real,Real.norm_eq_abs,
    abs_inv,abs_of_nonneg (norm_nonneg _),hn]

lemma normalized_coupling (H v w : Operator ι) :
    ‖⟪normalizedSeed v,PerturbedDynamics.liouvillian H (normalizedSeed w)⟫_ℂ‖^2 =
    ‖hsInner v (H*w-w*H)‖^2 / ((hsInner v v).re*(hsInner w w).re) := by
  simp only [normalizedSeed,map_smul,PerturbedDynamics.liouvillian_rowVectorize,
    inner_smul_left,inner_smul_right,norm_mul,Complex.norm_conj,
    Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    mul_pow,inv_pow,FactorTwo.rowVectorize_inner,row_norm_sq v,row_norm_sq w,hsInner]
  ring

/-- Identification at each individual Krylov degree, not just after summing
the complexity. Thus certificate probability tables are actual GS tables. -/
theorem actual_probability {d : ℕ} (H A : Operator ι)
    (hH : H.IsHermitian) (hA : A ≠ 0)
    (v : Fin d → Operator ι) (p : Fin d → Polynomial ℂ)
    (hp : ∀ i, v i = (Polynomial.aeval (FactorTwo.commutator H)) (p i) A)
    (hd : ∀ i, (p i).degree = (i.val : WithBot ℕ))
    (ho : Pairwise (fun i j => hsInner (v i) (v j)=0)) (i : Fin d) (t : ℝ) :
    ‖⟪gramSchmidtNormed ℂ
        (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H) (normalizedSeed A))
        i.val,
      TaylorRemainder.evolution (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian H))
        (normalizedSeed A) t⟫_ℂ‖^2 = UnitaryCovariance.matrixProbability H A (v i) t := by
  let Φ := polynomialMap H A
  let c : ℂ := (‖FactorTwo.rowVectorize A‖⁻¹ : ℝ)
  have hn : ‖FactorTwo.rowVectorize A‖ ≠ 0 := by
    intro hz
    apply hA
    exact FactorTwo.rowVectorize.injective (by simpa using norm_eq_zero.mp hz)
  have hcn : c ≠ 0 := by
    change (↑(‖FactorTwo.rowVectorize A‖⁻¹) : ℂ) ≠ 0
    exact_mod_cast inv_ne_zero hn
  have hv (j : Fin d) : Φ (p j) = c • FactorTwo.rowVectorize (v j) := by
    rw [hp j]
    rfl
  have hc (j : Fin d) : (p j).leadingCoeff ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro hz
    have h := hd j
    simp [hz] at h
  have hg : Pairwise (fun i j => ⟪Φ (p i),Φ (p j)⟫_ℂ=0) := by
    intro i j hij
    rw [hv,hv,inner_smul_left,inner_smul_right,FactorTwo.rowVectorize_inner]
    change star c * (c * hsInner (v i) (v j)) = 0
    rw [ho hij]
    simp
  have hraw := CertifiedGS.gramSchmidt_eq_inv_smul
    (fun n => Φ (Polynomial.X^n)) (fun j => Φ (p j))
    (fun j => (p j).leadingCoeff) hc
    (fun j => CertifiedGS.polynomial_triangular Φ (p j) j.val (hd j)) hg i
  have hf : (fun n => Φ (Polynomial.X^n)) =
      PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H) (normalizedSeed A) :=
    funext (polynomialMap_power H A)
  rw [← hf,gramSchmidtNormed,hraw]
  have hprob := CertifiedGS.normalized_multiple_probability
    ((p i).leadingCoeff⁻¹) (inv_ne_zero (hc i)) (Φ (p i))
    (TaylorRemainder.evolution (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian H))
      (normalizedSeed A) t)
  simp only [Complex.ofReal_inv] at hprob
  refine hprob.trans ?_
  rw [hv]
  exact scaled_probability H A (v i) hH t c hcn

end
end Krylov.CertifiedProbabilities
