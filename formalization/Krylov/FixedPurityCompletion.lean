import Krylov.PhysicalRatios

namespace Krylov.FixedPurityCompletion
open Matrix FamilyStates PhysicalRatios Ratios
noncomputable section

/-- The exact rational finite anchor printed in the manuscript appendix. -/
theorem rational_anchor : fixedState (1/10) =
    (1/100 : ℝ) • (!![66,0,0,0;0,24,0,0;0,0,5,3;0,0,3,5] : FourLevel) := by
  have hs : Real.sqrt (2*(1/10 : ℝ)-59*(1/10 : ℝ)^2/25) = 21/50 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fixedState,fixedPurityEigenPlus,fixedPurityEigenMinus,
      fixedPurityDiscriminant,hs,Matrix.smul_apply]

theorem rational_anchor_purity : trace (fixedState (1/10) * fixedState (1/10)) = (1/2 : ℝ) :=
  fixedState_purity (by norm_num) (by norm_num)

lemma lower_bound_large (M : ℝ) {ε : ℝ} (he : 0<ε)
    (hε : ε < 5/(18*(|M|+1))) :
    M < (5/(18*ε))*(1-ε/10) := by
  have hd : 0 < 18*(|M|+1) := by positivity
  have hm := (lt_div_iff₀ hd).mp hε
  have hb : |M|+1 < 5/(18*ε) := by
    apply (lt_div_iff₀ (by positivity : 0<18*ε)).mpr
    nlinarith
  have heq : (5/(18*ε))*(1-ε/10) = 5/(18*ε)-1/36 := by
    field_simp
    ring
  rw [heq]
  linarith [le_abs_self M]

/-- Uniform divergence means *every* sufficiently small positive parameter,
not just existence of an unbounded subsequence of witnesses. -/
theorem uniformly_diverges (M : ℝ) :
    ∃ ε₀>0, ∀ ε : ℝ, 0<ε → ε<ε₀ →
      (∀ t : ℝ, M < fixedContinuedRatio ε t) ∧
      M < Temporal.periodMean (fixedContinuedRatio ε) := by
  refine ⟨min (5/18) (5/(18*(|M|+1))), lt_min (by norm_num) (by positivity), ?_⟩
  intro ε he hε
  have he' : ε<5/18 := lt_of_lt_of_le hε (min_le_left _ _)
  have hl := lower_bound_large M he (lt_of_lt_of_le hε (min_le_right _ _))
  exact ⟨fun t => lt_of_lt_of_le hl (fixed_physical_uniform_bounds he he' t).1,
    lt_of_lt_of_le hl (fixed_physical_periodMean_bounds he he').1⟩

/-- Explicit uniform vanishing of the purity-rescaled reciprocal Pq, P=1/2. -/
theorem purity_reciprocal_uniform_small {δ : ℝ} (hδ : 0<δ) :
    ∃ ε₀>0, ∀ ε : ℝ, 0<ε → ε<ε₀ → ε<5/18 →
      ∀ t : ℝ, 0<(1/2)/fixedContinuedRatio ε t ∧
        (1/2)/fixedContinuedRatio ε t<δ := by
  obtain ⟨ε₀,hε₀,h⟩ := fixed_physical_reciprocal_uniform_small hδ
  refine ⟨ε₀,hε₀,?_⟩
  intro ε he he₀ he' t
  have ht := h ε he he₀ he' t
  have hid : (1/2 : ℝ)/fixedContinuedRatio ε t = (1/fixedContinuedRatio ε t)/2 := by ring
  rw [hid]
  constructor <;> linarith
end
end Krylov.FixedPurityCompletion
