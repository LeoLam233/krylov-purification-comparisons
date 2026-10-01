import Krylov.ConcreteChains

noncomputable section
namespace Krylov.FiniteOperator
open Matrix OperatorBridge ConcreteChains
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem hsInner_swap (A B : Operator ι) : star (hsInner A B) = hsInner B A := by
  simp only [hsInner,star_sum,star_mul',star_star]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem hsInner_sum_left (v : κ → Operator ι) (c : κ → ℂ) (B : Operator ι) :
    hsInner (∑ k, c k • v k) B = ∑ k, star (c k) * hsInner (v k) B := by
  rw [← hsInner_swap]
  change star (hsInnerLinearRight B (∑ k, c k • v k)) = _
  simp only [map_sum,map_smul,smul_eq_mul,map_mul,hsInnerLinearRight,
    LinearMap.coe_mk,AddHom.coe_mk,star_sum,star_mul',hsInner_swap]

theorem coefficient (v : κ → Operator ι) (d : κ → ℝ)
    (hg : ∀ k l, hsInner (v k) (v l) = if k=l then (d k : ℂ) else 0)
    (c : κ → ℂ) (k : κ) : hsInner (v k) (∑ l, c l • v l) = c k * d k := by
  change hsInnerLinearRight (v k) (∑ l, c l • v l) = _
  simp only [map_sum,map_smul,smul_eq_mul,hsInnerLinearRight,
    LinearMap.coe_mk,AddHom.coe_mk,hg,mul_ite,mul_zero]
  simp

/-- Finite Parseval in the orthogonal, not necessarily normalized, operator basis. -/
theorem parseval (v : κ → Operator ι) (d : κ → ℝ)
    (hg : ∀ k l, hsInner (v k) (v l) = if k=l then (d k : ℂ) else 0)
    (hd : ∀ k, 0 < d k) (x : Operator ι)
    (hx : x ∈ Submodule.span ℂ (Set.range v)) :
    ∑ k, Complex.normSq (hsInner (v k) x) / d k = (hsInner x x).re := by
  obtain ⟨c,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  rw [hsInner_sum_left]
  simp only [coefficient v d hg, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul,Complex.normSq_ofReal]
  have hnorm : star (c k) * c k = (Complex.normSq (c k) : ℂ) :=
    by simpa [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := c k)).symm
  have heq : star (c k) * (c k * (d k : ℂ)) = (Complex.normSq (c k) : ℂ) * d k := by
    rw [← mul_assoc,hnorm]
  rw [heq]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  field_simp [(hd k).ne']
  ring

/-- Exact normalization for any complete orthogonal finite operator chain. -/
theorem probability_sum (E : ι → ℝ) (A : Operator ι) (v : κ → Operator ι)
    (d : κ → ℝ) (s : ℝ) (t : ℝ)
    (hg : ∀ k l, hsInner (v k) (v l) = if k=l then (d k : ℂ) else 0)
    (hd : ∀ k, 0 < d k) (hs : 0 < s) (hA : (hsInner A A).re = s)
    (hx : diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ ∈
      Submodule.span ℂ (Set.range v))
    (hn : (hsInner (diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ)
      (diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ)).re = s) :
    ∑ k, chainProbability E A (v k) t = 1 := by
  have hp := parseval v d hg hd _ hx
  rw [hn] at hp
  simp only [chainProbability,hA,hg,↓reduceIte,Complex.ofReal_re]
  simp_rw [mul_comm s,← div_div]
  rw [← Finset.sum_div,hp,div_self hs.ne']

/-- Actual finite operator probabilities are continuous in time. -/
theorem continuous_chainProbability (E : ι → ℝ) (A v : Operator ι) :
    Continuous (fun t : ℝ => chainProbability E A v t) := by
  simp only [chainProbability,diagonalUnitary_conjugation,hsInner,spectralFilter,phase]
  fun_prop

theorem continuous_chainComplexity {m : ℕ} (E : ι → ℝ) (A : Operator ι)
    (v : Fin m → Operator ι) : Continuous (fun t : ℝ => chainComplexity E A v t) := by
  unfold chainComplexity
  apply continuous_finset_sum
  intro k _
  exact continuous_const.mul (continuous_chainProbability E A (v k))

end Krylov.FiniteOperator
