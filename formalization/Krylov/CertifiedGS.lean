import Krylov.KrylovTermination
import Mathlib.Algebra.Polynomial.Sequence

/-! Reusable identification of hand-certified finite orthogonal polynomial
chains with the actual normalized Gram--Schmidt complexity. -/
namespace Krylov.CertifiedGS
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def previousSpan (f : ℕ → E) (n : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ (f '' Set.Iio n)

def chainPrefix {d : ℕ} (v : Fin d → E) (n : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ (v '' {i | i.val < n})

lemma inner_zero_on_span {S : Set E} {x : E} (h : ∀ y ∈ S, ⟪x,y⟫_ℂ = 0) :
    ∀ y ∈ Submodule.span ℂ S, ⟪x,y⟫_ℂ = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp
  | add y z hy hz ihy ihz => simp [inner_add_right, ihy, ihz]
  | smul c y hy ih => simp [inner_smul_right, ih]

/-- An invertible lower-triangular change of an ordered list preserves each
strict prefix span, even if some evaluated vectors vanish. -/
theorem previousSpan_eq_chainPrefix {d : ℕ} (f : ℕ → E) (v : Fin d → E)
    (c : Fin d → ℂ) (hc : ∀ i, c i ≠ 0)
    (htri : ∀ i, v i - c i • f i.val ∈ previousSpan f i.val)
    (n : ℕ) (hn : n ≤ d) : previousSpan f n = chainPrefix v n := by
  have hv : ∀ i : Fin d, i.val < n → v i ∈ previousSpan f n := by
    intro i hi
    have hsub : previousSpan f i.val ≤ previousSpan f n :=
      Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hi.le))
    have hf : f i.val ∈ previousSpan f n := Submodule.subset_span ⟨i.val,hi,rfl⟩
    simpa using (previousSpan f n).add_mem (hsub (htri i))
      ((previousSpan f n).smul_mem (c i) hf)
  have hf : ∀ k, k < n → f k ∈ chainPrefix v n := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      let i : Fin d := ⟨k,lt_of_lt_of_le hk hn⟩
      have hprev : previousSpan f k ≤ chainPrefix v n := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j,hj,rfl⟩
        exact ih j hj (lt_trans hj hk)
      have hvi : v i ∈ chainPrefix v n := Submodule.subset_span ⟨i,hk,rfl⟩
      have hm := (chainPrefix v n).sub_mem hvi (hprev (htri i))
      have hs : c i • f k ∈ chainPrefix v n := by simpa using hm
      simpa only [smul_smul, inv_mul_cancel₀ (hc i), one_smul] using
        (chainPrefix v n).smul_mem (c i)⁻¹ hs
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,rfl⟩
    exact hf k hk
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact hv i hi

/-- Orthogonality plus a triangular certificate uniquely determines the raw
Gram--Schmidt vectors. Non-real phases and negative leading coefficients are
allowed, and zero evaluated vectors remain literal zeros. -/
theorem gramSchmidt_eq_inv_smul {d : ℕ} (f : ℕ → E) (v : Fin d → E)
    (c : Fin d → ℂ) (hc : ∀ i, c i ≠ 0)
    (htri : ∀ i, v i - c i • f i.val ∈ previousSpan f i.val)
    (ho : Pairwise (fun i j => ⟪v i,v j⟫_ℂ = 0)) (i : Fin d) :
    gramSchmidt ℂ f i.val = (c i)⁻¹ • v i := by
  let g := gramSchmidt ℂ f i.val
  let w := (c i)⁻¹ • v i
  have hw : ∀ y ∈ previousSpan f i.val, ⟪w,y⟫_ℂ = 0 := by
    rw [previousSpan_eq_chainPrefix f v c hc htri i.val i.isLt.le]
    apply inner_zero_on_span
    rintro _ ⟨j,hj,rfl⟩
    have hne : i ≠ j := by
      intro he; subst j; exact Nat.lt_irrefl _ hj
    simp only [w, inner_smul_left, ho hne, mul_zero]
  have hg : ∀ y ∈ previousSpan f i.val, ⟪g,y⟫_ℂ = 0 := by
    apply inner_zero_on_span
    rintro _ ⟨j,hj,rfl⟩
    exact gramSchmidt_inv_triangular ℂ f hj
  have hfw : f i.val - w ∈ previousSpan f i.val := by
    have h := (previousSpan f i.val).smul_mem (-(c i)⁻¹) (htri i)
    simpa only [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ (hc i),
      neg_one_smul, neg_smul, sub_neg_eq_add, neg_add_eq_sub, one_smul] using h
  have hfg : f i.val - g ∈ previousSpan f i.val := by
    rw [gramSchmidt_def' ℂ f i.val]
    simp only [g, add_sub_cancel_left]
    apply Submodule.sum_mem
    intro j hj
    rw [Submodule.orthogonalProjection_singleton]
    apply Submodule.smul_mem
    apply Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iio.mpr (Finset.mem_Iio.mp hj)))
    exact gramSchmidt_mem_span ℂ f le_rfl
  have hgw : g-w ∈ previousSpan f i.val := by
    simpa using (previousSpan f i.val).sub_mem hfw hfg
  have hz : g-w=0 := inner_self_eq_zero.mp (show ⟪g-w,g-w⟫_ℂ=0 by rw [inner_sub_left,hg _ hgw,hw _ hgw]; simp)
  exact sub_eq_zero.mp hz

/-- Normalizing a nonzero scalar multiple changes only its phase, so its
probability is the norm-divided probability of the certified vector. The
identity also includes the zero vector, using the ordinary totalized quotient. -/
lemma normalized_multiple_probability (c : ℂ) (hc : c ≠ 0) (v x : E) :
    ‖⟪(‖c • v‖⁻¹ : ℂ) • (c • v),x⟫_ℂ‖^2 =
      ‖⟪v,x⟫_ℂ‖^2 / ‖v‖^2 := by
  by_cases hv : v=0
  · simp [hv]
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp only [inner_smul_left, norm_mul, norm_star, Complex.norm_real,
    Real.norm_eq_abs, abs_inv, abs_norm, norm_smul]
  field_simp
  ring

/-- Exact phase decomposition of normalization. A negative real factor
therefore introduces only a minus sign; arbitrary complex factors introduce
only their unit-modulus phase. Zero vectors are included. -/
lemma normalize_smul_phase (c : ℂ) (v : E) :
    (‖c • v‖⁻¹ : ℂ) • (c • v) =
      (c / (‖c‖ : ℂ)) • ((‖v‖⁻¹ : ℂ) • v) := by
  rw [norm_smul]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, mul_inv_rev, smul_smul, div_eq_mul_inv]
  congr 1
  ring

lemma scalar_phase_norm (c : ℂ) (hc : c ≠ 0) : ‖c / (‖c‖ : ℂ)‖=1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.mpr hc)]

/-- The certified vector vanishes exactly at a terminating/padded GS index. -/
lemma normed_zero_iff_vector_zero {d : ℕ} (f : ℕ → E) (v : Fin d → E)
    (c : Fin d → ℂ) (hc : ∀ i, c i ≠ 0)
    (htri : ∀ i, v i-c i • f i.val ∈ previousSpan f i.val)
    (ho : Pairwise (fun i j => ⟪v i,v j⟫_ℂ=0)) (i : Fin d) :
    gramSchmidtNormed ℂ f i.val=0 ↔ v i=0 := by
  rw [KrylovTermination.normed_zero_iff,
    gramSchmidt_eq_inv_smul f v c hc htri ho i]
  simp [smul_eq_zero,hc i]

/-- Completeness of a triangular chain proves actual GS termination. -/
theorem normed_later_eq_zero_of_triangular {d : ℕ}
    (f : ℕ → E) (v : Fin d → E) (c : Fin d → ℂ) (hc : ∀ i, c i ≠ 0)
    (htri : ∀ i, v i-c i • f i.val ∈ previousSpan f i.val)
    (hcomplete : ∀ k, f k ∈ Submodule.span ℂ (Set.range v))
    (k : ℕ) (hk : d ≤ k) : gramSchmidtNormed ℂ f k=0 := by
  have hfull : previousSpan f d = Submodule.span ℂ (Set.range v) := by
    rw [previousSpan_eq_chainPrefix f v c hc htri d le_rfl]
    simp [chainPrefix, show {i : Fin d | i.val < d}=Set.univ by ext i; simp]
  apply (KrylovTermination.normed_zero_iff _ _).2
  apply (KrylovTermination.gram_zero_iff_mem _ _).2
  have hm : f k ∈ previousSpan f d := hfull.symm ▸ hcomplete k
  exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hk)) hm

/-- Finite summation is valid for a terminated GS sequence even if it contains
zero entries: the omitted GS indices contribute exactly zero. -/
theorem complexity_eq_finite_padded [FiniteDimensional ℂ E] {d : ℕ}
    (f : ℕ → E) (hlater : ∀ k, d ≤ k → gramSchmidtNormed ℂ f k=0) (x : E) :
    FactorTwoFinite.complexity f x =
      ∑ i : Fin d, (i.val : ℝ)*‖⟪gramSchmidtNormed ℂ f i.val,x⟫_ℂ‖^2 := by
  classical
  let e : FactorTwoFinite.GSIndex f → Fin d := fun k => ⟨k.val, by
    by_contra hn
    exact k.property (hlater k.val (Nat.le_of_not_gt hn))⟩
  have he : Function.Injective e := by
    intro i j hij
    exact Subtype.ext (congrArg Fin.val hij)
  apply Fintype.sum_of_injective e he
  · intro i hi
    have hz : gramSchmidtNormed ℂ f i.val=0 := by
      by_contra hn
      exact hi ⟨⟨i.val,hn⟩,Fin.ext rfl⟩
    simp [hz]
  · intro k
    rfl

/-- Complete orthogonal triangular certificates identify the generic weighted
GS complexity, including negative/complex phases and zero-padded endpoints. -/
theorem complexity_eq_of_triangular [FiniteDimensional ℂ E] {d : ℕ}
    (f : ℕ → E) (v : Fin d → E) (c : Fin d → ℂ) (hc : ∀ i, c i ≠ 0)
    (htri : ∀ i, v i-c i • f i.val ∈ previousSpan f i.val)
    (ho : Pairwise (fun i j => ⟪v i,v j⟫_ℂ=0))
    (hcomplete : ∀ k, f k ∈ Submodule.span ℂ (Set.range v)) (x : E) :
    FactorTwoFinite.complexity f x =
      ∑ i : Fin d, (i.val : ℝ)*(‖⟪v i,x⟫_ℂ‖^2 / ‖v i‖^2) := by
  rw [complexity_eq_finite_padded f
    (normed_later_eq_zero_of_triangular f v c hc htri hcomplete)]
  apply Finset.sum_congr rfl
  intro i _
  rw [gramSchmidtNormed,gramSchmidt_eq_inv_smul f v c hc htri ho i]
  congr 1
  simpa only [Complex.ofReal_inv] using
    normalized_multiple_probability ((c i)⁻¹) (inv_ne_zero (hc i)) (v i) x

/-- A linear polynomial evaluator sends every polynomial of degree below n
into the strict prefix of its power sequence. -/
lemma polynomial_mem_previousSpan (Φ : Polynomial ℂ →ₗ[ℂ] E)
    (p : Polynomial ℂ) (n : ℕ) (hp : p.degree < (n : WithBot ℕ)) :
    Φ p ∈ previousSpan (fun k => Φ (Polynomial.X^k)) n := by
  classical
  rw [← Polynomial.sum_C_mul_X_pow_eq p]
  simp only [Polynomial.sum, map_sum, ← Polynomial.smul_eq_C_mul, map_smul]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨k,?_,rfl⟩
  exact WithBot.coe_lt_coe.mp ((Polynomial.le_degree_of_mem_supp k hk).trans_lt hp)

/-- The leading coefficient is the invertible triangular diagonal of a
polynomial chain; the lower-degree remainder is a genuine previous-power
combination, not an additional chain hypothesis. -/
lemma polynomial_triangular (Φ : Polynomial ℂ →ₗ[ℂ] E)
    (p : Polynomial ℂ) (n : ℕ) (hp : p.degree=(n : WithBot ℕ)) :
    Φ p-p.leadingCoeff • Φ (Polynomial.X^n) ∈
      previousSpan (fun k => Φ (Polynomial.X^k)) n := by
  have hp0 : p ≠ 0 := by intro h; simpa [h] using hp
  have hn : p.natDegree=n := Polynomial.natDegree_eq_of_degree_eq_some hp
  have hc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hdeg : (p.leadingCoeff • (Polynomial.X^n : Polynomial ℂ)).degree=p.degree := by
    rw [Polynomial.smul_eq_C_mul,Polynomial.degree_C_mul hc,Polynomial.degree_X_pow,hp]
  have hlc : (p.leadingCoeff • (Polynomial.X^n : Polynomial ℂ)).leadingCoeff=p.leadingCoeff := by
    simp [Polynomial.smul_eq_C_mul, Polynomial.leadingCoeff_mul]
  have hrem : (p-p.leadingCoeff • (Polynomial.X^n : Polynomial ℂ)).degree < (n : WithBot ℕ) := by
    rw [← hp]
    exact Polynomial.degree_sub_lt hdeg.symm hp0 hlc.symm
  simpa only [map_sub,map_smul] using
    polynomial_mem_previousSpan Φ _ n hrem

/-- Main polynomial bridge. Correct degree already implies a nonzero leading
coefficient; its sign, phase, and magnitude need no convention. Completeness
proves actual termination, and zero evaluated polynomials are harmless padding. -/
theorem complexity_eq_of_polynomials [FiniteDimensional ℂ E] {d : ℕ}
    (Φ : Polynomial ℂ →ₗ[ℂ] E) (p : Fin d → Polynomial ℂ)
    (hdegree : ∀ i, (p i).degree=(i.val : WithBot ℕ))
    (ho : Pairwise (fun i j => ⟪Φ (p i),Φ (p j)⟫_ℂ=0))
    (hcomplete : ∀ k, Φ (Polynomial.X^k) ∈
      Submodule.span ℂ (Set.range (fun i => Φ (p i)))) (x : E) :
    FactorTwoFinite.complexity (fun k => Φ (Polynomial.X^k)) x =
      ∑ i : Fin d, (i.val : ℝ)*(‖⟪Φ (p i),x⟫_ℂ‖^2 / ‖Φ (p i)‖^2) := by
  apply complexity_eq_of_triangular _ _ (fun i => (p i).leadingCoeff) _ _ ho hcomplete
  · intro i
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro hz
    have hd := hdegree i
    simp [hz] at hd
  · intro i
    exact polynomial_triangular Φ (p i) i.val (hdegree i)

/-- Scalar normalization of the evolved target scales every probability by
the same squared norm, including terminated and zero-padded chains. -/
lemma complexity_smul_target [FiniteDimensional ℂ E]
    (f : ℕ → E) (a : ℂ) (x : E) :
    FactorTwoFinite.complexity f (a • x) =
      ‖a‖^2 * FactorTwoFinite.complexity f x := by
  unfold FactorTwoFinite.complexity FactorTwoFinite.probability
  simp only [inner_smul_right,norm_mul,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end Krylov.CertifiedGS
