import Krylov.CertifiedFamilyGS

/-! Closed-interval three-atom GS identification, including both genuinely
terminated endpoints. This is a finite-support certificate, not a limit proof. -/
namespace Krylov.CertifiedThreeAtomGS
open Matrix OperatorBridge ConcreteChains
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact symmetric spectral weights on the full physically admissible closed
mass interval. The endpoint chains may contain literal zero padding. -/
structure Data (E : ι → ℝ) (A : Operator ι) (μ s : ℝ) : Prop where
  scale_pos : 0 < s
  mass_nonneg : 0 ≤ μ
  mass_le : μ ≤ 1
  support : ∀ i j, A i j ≠ 0 → E i-E j = -1 ∨ E i-E j = 0 ∨ E i-E j = 1
  weight_neg : gapWeight E A (-1)=s*μ/2
  weight_zero : gapWeight E A 0=s*(1-μ)
  weight_pos : gapWeight E A 1=s*μ/2

variable {E : ι → ℝ} {A : Operator ι} {μ s : ℝ}

lemma inner_filters (h : Data E A μ s) (f g : ℝ → ℂ) :
    hsInner (spectralFilter E f A) (spectralFilter E g A) =
      (s*μ/2 : ℝ)*star (f (-1))*g (-1)+
      (s*(1-μ) : ℝ)*star (f 0)*g 0+
      (s*μ/2 : ℝ)*star (f 1)*g 1 := by
  have hsupp : ∀ i j, A i j ≠ 0 → E i-E j ∈ ({-1,0,1} : Finset ℝ) := by
    intro i j hn
    rcases h.support i j hn with ha | ha | ha <;> simp [ha]
  rw [hsInner_filters_supported E f g A {-1,0,1} hsupp]
  norm_num [h.weight_neg,h.weight_zero,h.weight_pos]
  ring

lemma gram (h : Data E A μ s) (k l : Fin 3) :
    hsInner (ThreeAtomOperator.chain E A μ k) (ThreeAtomOperator.chain E A μ l) =
      if k=l then ((s*ThreeAtomOperator.norms μ k : ℝ) : ℂ) else 0 := by
  simp only [ThreeAtomOperator.chain,polynomial_eq_spectralFilter]
  rw [inner_filters h]
  fin_cases k <;> fin_cases l <;>
    norm_num [ThreeAtomOperator.polynomial,ThreeAtomOperator.norms,Complex.star_def] <;> ring

lemma seed_norm (h : Data E A μ s) : hsInner A A=(s : ℂ) := by
  simpa [ThreeAtomOperator.chain_zero,ThreeAtomOperator.norms] using gram h 0 0

lemma ordered_recurrence (h : Data E A μ s) (k : Fin 3) :
    liouvillian E (ThreeAtomOperator.chain E A μ k) =
      (if hk : k.val+1<3 then ThreeAtomOperator.chain E A μ ⟨k.val+1,hk⟩ else 0)+
      (if hk : 0<k.val then (ThreeAtomOperator.bSquared μ k : ℂ) •
        ThreeAtomOperator.chain E A μ ⟨k.val-1,by omega⟩ else 0) := by
  ext i j
  by_cases hz : A i j=0
  · fin_cases k <;> simp [liouvillian,ThreeAtomOperator.chain_entry,ThreeAtomOperator.polynomial,hz]
  · change ((E i-E j : ℝ) : ℂ)*ThreeAtomOperator.chain E A μ k i j = _
    rcases h.support i j hz with hg | hg | hg <;>
      rw [hg] <;> fin_cases k <;>
      simp [ThreeAtomOperator.chain_entry,ThreeAtomOperator.polynomial,ThreeAtomOperator.bSquared,hg] <;> ring

lemma chain_spans_cyclic (h : Data E A μ s) :
    Submodule.span ℂ (Set.range (ThreeAtomOperator.chain E A μ))=cyclicSpan (liouvillian E) A := by
  apply span_polynomial_chain_eq_cyclic (liouvillian E) A
    (ThreeAtomOperator.chain E A μ) (ThreeAtomOperator.polynomial μ)
  · intro k; rfl
  · exact Submodule.subset_span ⟨0,ThreeAtomOperator.chain_zero E A μ⟩
  · intro k
    rw [ordered_recurrence h]
    apply Submodule.add_mem
    · split_ifs with hk
      · exact Submodule.subset_span ⟨_,rfl⟩
      · exact Submodule.zero_mem _
    · split_ifs with hk
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,rfl⟩)
      · exact Submodule.zero_mem _

lemma matrix_eq_zero_of_self_inner {B : Operator ι} (hB : hsInner B B=0) : B=0 := by
  apply FactorTwo.rowVectorize.injective
  rw [map_zero]
  exact inner_self_eq_zero.mp (show ⟪FactorTwo.rowVectorize B,FactorTwo.rowVectorize B⟫_ℂ=0 by
    rw [FactorTwo.rowVectorize_inner]
    exact hB)

/-- At μ=0 the two later displayed vectors really are zero, so they are
padding of a stationary one-dimensional chain. -/
lemma zero_mass_padding (h : Data E A 0 s) :
    ThreeAtomOperator.chain E A 0 1=0 ∧ ThreeAtomOperator.chain E A 0 2=0 := by
  constructor
  · apply matrix_eq_zero_of_self_inner
    simpa [ThreeAtomOperator.norms] using gram h 1 1
  · apply matrix_eq_zero_of_self_inner
    simpa [ThreeAtomOperator.norms] using gram h 2 2

/-- At μ=1 the quadratic vector vanishes exactly: the process is two-atom. -/
lemma unit_mass_padding (h : Data E A 1 s) : ThreeAtomOperator.chain E A 1 2=0 := by
  apply matrix_eq_zero_of_self_inner
  simpa [ThreeAtomOperator.norms] using gram h 2 2

/-- The literal generic GS complexity equals the displayed chain sum on the
entire mass interval, including the stationary and two-atom endpoints. -/
theorem actual_eq_chainComplexity (h : Data E A μ s) (t : ℝ) :
    PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian (hamiltonian E))
      (PhysicalCurvatureNecessary.normalizedSeed A) t =
        chainComplexity E A (ThreeAtomOperator.chain E A μ) t := by
  have hA : A ≠ 0 := by
    intro hz
    have hh := seed_norm h
    simp [hz,hsInner] at hh
    exact h.scale_pos.ne' (Complex.ofReal_eq_zero.mp hh.symm)
  apply CertifiedFamilyGS.actual_eq_chainComplexity E A hA _ (ThreeAtomOperator.polynomial μ)
  · intro i; rfl
  · exact CertifiedPolynomialDegrees.three μ
  · intro i j hij
    simp [gram h,hij]
  · exact chain_spans_cyclic h

lemma evolved_amplitude (h : Data E A μ s) (k : Fin 3) (t : ℝ) :
    hsInner (ThreeAtomOperator.chain E A μ k)
      (diagonalUnitary E t*A*(diagonalUnitary E t)ᴴ) =
      (![ ((s*(1-μ+μ*Real.cos t) : ℝ) : ℂ),
          -Complex.I*(s*μ*Real.sin t : ℝ),
          ((s*μ*(1-μ)*(Real.cos t-1) : ℝ) : ℂ)] : Fin 3 → ℂ) k := by
  rw [ThreeAtomOperator.chain,polynomial_eq_spectralFilter,
    diagonalUnitary_conjugation,inner_filters h]
  fin_cases k <;> apply Complex.ext <;>
    simp [ThreeAtomOperator.polynomial,phase,Complex.star_def,Complex.exp_re,Complex.exp_im,
      Complex.mul_re,Complex.mul_im,← Complex.ofReal_cos,← Complex.ofReal_sin] <;> ring

/-- Closed formula with both endpoint cases established directly in Lean. -/
theorem actual_eq_threeAtom (h : Data E A μ s) (t : ℝ) :
    PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian (hamiltonian E))
      (PhysicalCurvatureNecessary.normalizedSeed A) t = Qubit.threeAtom μ t := by
  rw [actual_eq_chainComplexity h]
  by_cases hm0 : μ=0
  · subst μ
    simp [chainComplexity,chainProbability,gram h,ThreeAtomOperator.norms,
      Fin.sum_univ_succ,Qubit.threeAtom]
  by_cases hm1 : μ=1
  · subst μ
    have hs : s ≠ 0 := h.scale_pos.ne'
    simp only [chainComplexity,chainProbability,evolved_amplitude h,seed_norm h,gram h]
    norm_num [Fin.sum_univ_succ,ThreeAtomOperator.norms,Qubit.threeAtom,
      Complex.normSq_mul,Complex.normSq_ofReal,Complex.normSq_apply,← Complex.ofReal_sin]
    field_simp
    ring
  · exact ThreeAtomOperator.complexity_eq_threeAtom
      ⟨h.scale_pos,lt_of_le_of_ne h.mass_nonneg (Ne.symm hm0),
        lt_of_le_of_ne h.mass_le hm1,h.support,h.weight_neg,h.weight_zero,h.weight_pos⟩ t

end
end Krylov.CertifiedThreeAtomGS
