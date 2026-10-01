import Krylov.PhysicalTemporal

/-!
# Pointwise removable zeros of actual five-node complexities

The complete physical operator amplitudes are evaluated explicitly. Their
index-weighted probability sum factors as `(1-cos t) * reducedComplexity`.
The reduced factor is continuous and strictly positive throughout `cos t ∈ [-1,1]`,
including the common recurrence value `2*m2`. This supplies genuine pointwise
continuous ratio extensions independently of the existing null-set CV proofs.
-/

noncomputable section
namespace Krylov.FiveAtomRemovable
open Matrix OperatorBridge ConcreteChains FiveAtom
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : ι → ℝ} {A : Operator ι} {u v s : ℝ}

/-- Even degree-two amplitude after its common recurrence factor is removed. -/
def evenFactor (u v z : ℝ) : ℝ :=
  u * (1 - m2 u v) + 2 * v * (4 - m2 u v) * (1 + z)

/-- The five polynomial-chain amplitude numerators, with the common seed norm removed. -/
def amplitudes (u v t : ℝ) : Fin 5 → ℂ :=
  ![⟨returnAmplitude u v t, 0⟩,
    ⟨0, -Real.sin t * (u + 4 * v * Real.cos t)⟩,
    ⟨-(1 - Real.cos t) * evenFactor u v (Real.cos t), 0⟩,
    ⟨0, 12 * u * v * Real.sin t * (1 - Real.cos t)⟩,
    ⟨24 * zeroMass u v * u * v * (1 - Real.cos t) ^ 2, 0⟩]

private theorem phase_eq (ω t : ℝ) :
    phase ω t = (Real.cos (ω * t) : ℂ) - Complex.I * (Real.sin (ω * t) : ℂ) := by
  unfold phase
  rw [Complex.exp_mul_I]
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem evolved_amplitude (h : Data E A u v s) (k : Fin 5) (t : ℝ) :
    hsInner (chain E A u v k)
      (diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ) =
      (s : ℂ) * amplitudes u v t k := by
  rw [chain, polynomial_eq_spectralFilter, diagonalUnitary_conjugation, inner_filters h]
  fin_cases k <;>
    norm_num [polynomial, phase_eq, Complex.star_def, nodes, weights, amplitudes,
      Complex.mk_eq_add_mul_I, returnAmplitude, evenFactor, Fin.sum_univ_succ,
      Real.cos_two_mul, Real.sin_two_mul, m2, m4, m6, n2, zeroMass] <;>
    push_cast <;>
    simp only [mul_comm (t : ℂ) 2, Complex.cos_two_mul, Complex.sin_two_mul] <;> ring

/-- Probability formulas derived from the actual matrix-evolution amplitudes. -/
def probabilities (u v t : ℝ) : Fin 5 → ℝ :=
  ![returnAmplitude u v t ^ 2,
    Real.sin t ^ 2 * (u + 4 * v * Real.cos t) ^ 2 / m2 u v,
    (1 - Real.cos t) ^ 2 * evenFactor u v (Real.cos t) ^ 2 / n2 u v,
    4 * u * v * Real.sin t ^ 2 * (1 - Real.cos t) ^ 2 / m2 u v,
    4 * zeroMass u v * u * v * (1 - Real.cos t) ^ 4 / n2 u v]

theorem chainProbability_eq (h : Data E A u v s) (k : Fin 5) (t : ℝ) :
    chainProbability E A (chain E A u v k) t = probabilities u v t k := by
  rw [chainProbability, evolved_amplitude h, seed_norm h, gram h]
  simp only [↓reduceIte, Complex.ofReal_re]
  have hs : s ≠ 0 := h.scale_pos.ne'
  have hu : u ≠ 0 := h.mass_one_pos.ne'
  have hv : v ≠ 0 := h.mass_two_pos.ne'
  have hz : zeroMass u v ≠ 0 := h.mass_zero_pos.ne'
  have hm : m2 u v ≠ 0 := (m2_pos h).ne'
  have hn : n2 u v ≠ 0 := (n2_pos h).ne'
  fin_cases k <;>
    norm_num [norms, amplitudes, probabilities, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
    field_simp <;> ring

/-- The recurrence-cancelled positive factor of the full complexity. -/
def reducedComplexity (u v z : ℝ) : ℝ :=
  (1 + z) * (u + 4 * v * z) ^ 2 / m2 u v +
  2 * (1 - z) * evenFactor u v z ^ 2 / n2 u v +
  12 * u * v * (1 + z) * (1 - z) ^ 2 / m2 u v +
  16 * zeroMass u v * u * v * (1 - z) ^ 3 / n2 u v

/-- Exact common-factor cancellation for genuine operator Krylov complexity. -/
theorem complexity_factor (h : Data E A u v s) (t : ℝ) :
    chainComplexity E A (chain E A u v) t =
      (1 - Real.cos t) * reducedComplexity u v (Real.cos t) := by
  unfold chainComplexity
  simp only [chainProbability_eq h]
  norm_num [probabilities, Fin.sum_univ_succ]
  have hs : Real.sin t ^ 2 = (1 - Real.cos t) * (1 + Real.cos t) := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hs]
  unfold reducedComplexity
  ring

theorem reduced_at_one (h : Data E A u v s) : reducedComplexity u v 1 = 2 * m2 u v := by
  have hm : m2 u v ≠ 0 := (m2_pos h).ne'
  simp [reducedComplexity, m2] at *
  field_simp
  ring

theorem reduced_pos (h : Data E A u v s) {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    0 < reducedComplexity u v z := by
  have hu := h.mass_one_pos
  have hv := h.mass_two_pos
  have h0 := h.mass_zero_pos
  have hm := m2_pos h
  have hn := n2_pos h
  by_cases heq : z = 1
  · rw [heq, reduced_at_one h]
    positivity
  · have hz1 : 0 < 1 - z := sub_pos.mpr (lt_of_le_of_ne hz.2 heq)
    have hz0 : 0 ≤ 1 + z := by linarith [hz.1]
    have h1 : 0 ≤ (1 + z) * (u + 4 * v * z) ^ 2 / m2 u v := by positivity
    have h2 : 0 ≤ 2 * (1 - z) * evenFactor u v z ^ 2 / n2 u v := by positivity
    have h3 : 0 ≤ 12 * u * v * (1 + z) * (1 - z) ^ 2 / m2 u v := by positivity
    have h4 : 0 < 16 * zeroMass u v * u * v * (1 - z) ^ 3 / n2 u v := by positivity
    unfold reducedComplexity
    linarith

theorem reduced_continuous (u v : ℝ) : Continuous (reducedComplexity u v) := by
  unfold reducedComplexity evenFactor
  fun_prop

theorem reduced_cos_pos (h : Data E A u v s) (t : ℝ) :
    0 < reducedComplexity u v (Real.cos t) :=
  reduced_pos h ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩

/-- The actual complexity vanishes exactly at the common period recurrences. -/
theorem complexity_zero_iff (h : Data E A u v s) (t : ℝ) :
    chainComplexity E A (chain E A u v) t = 0 ↔ Real.cos t = 1 := by
  rw [complexity_factor h]
  have hp := (reduced_cos_pos h t).ne'
  simp only [mul_eq_zero, hp, or_false, sub_eq_zero]
  exact eq_comm

/-- Continuous quotient of the recurrence-cancelled factors. -/
def ratioExtension (u v U V t : ℝ) : ℝ :=
  reducedComplexity u v (Real.cos t) / reducedComplexity U V (Real.cos t)

variable {B : Operator ι} {U V S : ℝ}

theorem ratioExtension_continuous (hD : Data E B U V S) :
    Continuous (ratioExtension u v U V) := by
  apply ((reduced_continuous u v).comp Real.continuous_cos).div
    ((reduced_continuous U V).comp Real.continuous_cos)
  intro t
  exact (reduced_cos_pos hD t).ne'

theorem ratioExtension_pos (hN : Data E A u v s) (hD : Data E B U V S) (t : ℝ) :
    0 < ratioExtension u v U V t :=
  div_pos (reduced_cos_pos hN t) (reduced_cos_pos hD t)

theorem ratio_eq_extension (hN : Data E A u v s) (hD : Data E B U V S)
    {t : ℝ} (ht : Real.cos t ≠ 1) :
    chainComplexity E A (chain E A u v) t / chainComplexity E B (chain E B U V) t =
      ratioExtension u v U V t := by
  rw [complexity_factor hN, complexity_factor hD]
  exact mul_div_mul_left _ _ (sub_ne_zero.mpr (Ne.symm ht))

theorem ratioExtension_recurrence (hN : Data E A u v s) (hD : Data E B U V S)
    {t₀ : ℝ} (ht : Real.cos t₀ = 1) :
    ratioExtension u v U V t₀ = m2 u v / m2 U V := by
  unfold ratioExtension
  rw [ht, reduced_at_one hN, reduced_at_one hD]
  exact mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)

/-- Recurrences are isolated, so the raw total quotient has the usual two-sided
punctured limit, not merely a limit taken along a specially restricted sequence. -/
theorem eventually_nonrecurrence {t₀ : ℝ} (ht : Real.cos t₀ = 1) :
    ∀ᶠ t in nhdsWithin t₀ ({t₀}ᶜ), Real.cos t ≠ 1 := by
  have hL : ∀ᶠ t in nhds t₀, t₀ - Real.pi < t :=
    eventually_gt_nhds (by linarith [Real.pi_pos])
  have hR : ∀ᶠ t in nhds t₀, t < t₀ + Real.pi :=
    eventually_lt_nhds (by linarith [Real.pi_pos])
  filter_upwards [hL.filter_mono nhdsWithin_le_nhds,
    hR.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hL hR hne
  change t ≠ t₀ at hne
  intro hc
  have hs : Real.sin t₀ = 0 := Real.sin_eq_zero_iff_cos_eq.2 (Or.inl ht)
  have hsub : Real.cos (t - t₀) = 1 := by
    rw [Real.cos_sub, hc, ht, hs]
    ring
  have heq := (Real.cos_eq_one_iff_of_lt_of_lt
    (by linarith [Real.pi_pos] : -(2 * Real.pi) < t - t₀)
    (by linarith [Real.pi_pos] : t - t₀ < 2 * Real.pi)).1 hsub
  exact hne (sub_eq_zero.mp heq)

/-- Finite strictly positive two-sided limit at every common recurrence. -/
theorem ratio_removable_limit (hN : Data E A u v s) (hD : Data E B U V S)
    {t₀ : ℝ} (ht : Real.cos t₀ = 1) :
    Filter.Tendsto
      (fun t => chainComplexity E A (chain E A u v) t /
        chainComplexity E B (chain E B U V) t)
      (nhdsWithin t₀ ({t₀}ᶜ)) (nhds (m2 u v / m2 U V)) ∧
      0 < m2 u v / m2 U V := by
  constructor
  · have hcont : Filter.Tendsto (ratioExtension u v U V) (nhds t₀)
        (nhds (ratioExtension u v U V t₀)) :=
      (ratioExtension_continuous (u := u) (v := v) hD).continuousAt.tendsto
    rw [ratioExtension_recurrence hN hD ht] at hcont
    apply (hcont.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [eventually_nonrecurrence ht] with t hneq
    exact (ratio_eq_extension hN hD hneq).symm
  · exact div_pos (m2_pos hN) (m2_pos hD)

theorem ratioExtension_periodic (u v U V : ℝ) :
    Function.Periodic (ratioExtension u v U V) (2 * Real.pi) := by
  intro t
  simp [ratioExtension, Real.cos_add_two_pi]

end Krylov.FiveAtomRemovable
