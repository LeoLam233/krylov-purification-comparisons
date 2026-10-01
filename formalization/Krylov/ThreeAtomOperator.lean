import Krylov.ConcreteChains
import Krylov.FamilyStates

/-!
# Actual operator Krylov chains for a symmetric three-atom spectral measure

The vectors below are polynomials of the actual matrix commutator. Their
orthogonality, ordered recurrence, cyclic completeness, and probabilities
under diagonal-unitary conjugation are derived from the seed's gap weights.
-/
noncomputable section
namespace Krylov.ThreeAtomOperator
open Matrix OperatorBridge ConcreteChains
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact nondegenerate symmetric three-atom spectral data for an operator seed.
`s` is its (unnormalized) squared Hilbert--Schmidt norm. -/
structure Data (E : ι → ℝ) (A : Operator ι) (μ s : ℝ) : Prop where
  scale_pos : 0 < s
  mass_pos : 0 < μ
  mass_lt : μ < 1
  support : ∀ i j, A i j ≠ 0 → E i - E j = -1 ∨ E i - E j = 0 ∨ E i - E j = 1
  weight_neg : gapWeight E A (-1) = s * μ / 2
  weight_zero : gapWeight E A 0 = s * (1 - μ)
  weight_pos : gapWeight E A 1 = s * μ / 2

def polynomial (μ : ℝ) : Fin 3 → Polynomial ℂ :=
  ![1, Polynomial.X, Polynomial.X ^ 2 - Polynomial.C (μ : ℂ)]

def chain (E : ι → ℝ) (A : Operator ι) (μ : ℝ) (k : Fin 3) : Operator ι :=
  (Polynomial.aeval (liouvillian E)) (polynomial μ k) A

def norms (μ : ℝ) : Fin 3 → ℝ := ![1, μ, μ * (1 - μ)]
def bSquared (μ : ℝ) : Fin 3 → ℝ := ![0, μ, 1 - μ]

theorem chain_entry (E : ι → ℝ) (A : Operator ι) (μ : ℝ) (k : Fin 3) (i j : ι) :
    chain E A μ k i j = (polynomial μ k).eval ((E i - E j : ℝ) : ℂ) * A i j :=
  polynomial_liouvillian_entry _ _ _ _ _

theorem chain_zero (E : ι → ℝ) (A : Operator ι) (μ : ℝ) : chain E A μ 0 = A := by
  ext i j; simp [chain_entry, polynomial]

variable {E : ι → ℝ} {A : Operator ι} {μ s : ℝ}

private theorem supported (h : Data E A μ s) :
    ∀ i j, A i j ≠ 0 → E i - E j ∈ ({-1,0,1} : Finset ℝ) := by
  intro i j hn
  rcases h.support i j hn with ha | ha | ha <;> simp [ha]

theorem inner_filters (h : Data E A μ s) (f g : ℝ → ℂ) :
    hsInner (spectralFilter E f A) (spectralFilter E g A) =
      (s * μ / 2 : ℝ) * star (f (-1)) * g (-1) +
      (s * (1 - μ) : ℝ) * star (f 0) * g 0 +
      (s * μ / 2 : ℝ) * star (f 1) * g 1 := by
  rw [hsInner_filters_supported E f g A {-1,0,1} (supported h)]
  norm_num [h.weight_neg, h.weight_zero, h.weight_pos]
  ring

theorem gram (h : Data E A μ s) (k l : Fin 3) :
    hsInner (chain E A μ k) (chain E A μ l) =
      if k = l then ((s * norms μ k : ℝ) : ℂ) else 0 := by
  simp only [chain, polynomial_eq_spectralFilter]
  rw [inner_filters h]
  fin_cases k <;> fin_cases l <;>
    norm_num [polynomial, norms, Complex.star_def] <;> ring

theorem seed_norm (h : Data E A μ s) : hsInner A A = (s : ℂ) := by
  have hg := gram h 0 0
  simpa [chain_zero, norms] using hg

theorem chain_norm_pos (h : Data E A μ s) (k : Fin 3) :
    0 < (hsInner (chain E A μ k) (chain E A μ k)).re := by
  rw [gram h]
  simp only [↓reduceIte, Complex.ofReal_re]
  have h0 := h.scale_pos
  have h1 := h.mass_pos
  have h2 : 0 < 1 - μ := sub_pos.mpr h.mass_lt
  fin_cases k <;> norm_num [norms] <;> positivity

theorem normalized_chain_orthonormal (h : Data E A μ s) (k l : Fin 3) :
    hsInner (normalized (chain E A μ k)) (normalized (chain E A μ l)) =
      if k = l then 1 else 0 := by
  by_cases he : k = l
  · subst l; simp only [↓reduceIte]
    exact normalized_unit _ (chain_norm_pos h k)
  · simp [normalized, hsInner_smul, gram h, he]

theorem chain_linearIndependent (h : Data E A μ s) : LinearIndependent ℂ (chain E A μ) := by
  apply linearIndependent_of_hsGram _ (fun k => (s * norms μ k : ℝ)) (gram h)
  intro k
  have hp := chain_norm_pos h k
  rw [gram h] at hp
  simp only [↓reduceIte, Complex.ofReal_re] at hp
  exact Complex.ofReal_ne_zero.mpr hp.ne'

/-- The exact ordered three-term recurrence, before rescaling each vector to unit norm. -/
theorem ordered_recurrence (h : Data E A μ s) (k : Fin 3) :
    liouvillian E (chain E A μ k) =
      (if hk : k.val + 1 < 3 then chain E A μ ⟨k.val + 1,hk⟩ else 0) +
      (if hk : 0 < k.val then
        (bSquared μ k : ℂ) • chain E A μ ⟨k.val - 1, by omega⟩ else 0) := by
  ext i j
  by_cases hz : A i j = 0
  · fin_cases k <;> simp [liouvillian, chain_entry, polynomial, hz]
  · change ((E i - E j : ℝ) : ℂ) * chain E A μ k i j = _
    rcases h.support i j hz with hg | hg | hg <;>
      rw [hg] <;> fin_cases k <;>
      simp [chain_entry, polynomial, bSquared, hg] <;> ring

theorem chain_spans_cyclic (h : Data E A μ s) :
    Submodule.span ℂ (Set.range (chain E A μ)) = cyclicSpan (liouvillian E) A := by
  apply span_polynomial_chain_eq_cyclic (liouvillian E) A (chain E A μ) (polynomial μ)
  · intro k; rfl
  · exact Submodule.subset_span ⟨0, chain_zero E A μ⟩
  · intro k
    rw [ordered_recurrence h]
    apply Submodule.add_mem
    · split_ifs with hk
      · exact Submodule.subset_span ⟨_, rfl⟩
      · exact Submodule.zero_mem _
    · split_ifs with hk
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · exact Submodule.zero_mem _

theorem cyclic_dimension (h : Data E A μ s) :
    Module.finrank ℂ (cyclicSpan (liouvillian E) A) = 3 := by
  rw [← chain_spans_cyclic h]
  simpa using finrank_span_eq_card (chain_linearIndependent h)

/-- Actual complex amplitudes under the matrix exponential conjugation. -/
theorem evolved_amplitude (h : Data E A μ s) (k : Fin 3) (t : ℝ) :
    hsInner (chain E A μ k)
      (diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ) =
      (![ ((s * (1 - μ + μ * Real.cos t) : ℝ) : ℂ),
          -Complex.I * (s * μ * Real.sin t : ℝ),
          ((s * μ * (1 - μ) * (Real.cos t - 1) : ℝ) : ℂ)] : Fin 3 → ℂ) k := by
  rw [chain, polynomial_eq_spectralFilter, diagonalUnitary_conjugation, inner_filters h]
  fin_cases k <;> apply Complex.ext <;>
    simp [polynomial, phase, Complex.star_def, Complex.exp_re, Complex.exp_im,
      Complex.mul_re, Complex.mul_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin] <;> ring

/-- Each displayed probability is proved from a normalized Hilbert--Schmidt amplitude. -/
theorem probabilities (h : Data E A μ s) (k : Fin 3) (t : ℝ) :
    chainProbability E A (chain E A μ k) t =
      (![Qubit.prob0 μ t, Qubit.prob1 μ t, Qubit.prob2 μ t] : Fin 3 → ℝ) k := by
  rw [chainProbability, evolved_amplitude h, seed_norm h, gram h]
  simp only [↓reduceIte, Complex.ofReal_re]
  have hs : s ≠ 0 := h.scale_pos.ne'
  have hm : μ ≠ 0 := h.mass_pos.ne'
  have hm1 : 1 - μ ≠ 0 := (sub_pos.mpr h.mass_lt).ne'
  fin_cases k <;>
    norm_num [norms, Qubit.prob0, Qubit.prob1, Qubit.prob2,
      Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_apply,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im] <;>
    field_simp <;> ring

/-- Probability conservation for the complete physical operator chain. -/
theorem probabilities_sum (h : Data E A μ s) (t : ℝ) :
    ∑ k, chainProbability E A (chain E A μ k) t = 1 := by
  simp only [probabilities h]
  simpa [Fin.sum_univ_succ, add_assoc] using Qubit.probabilities_sum μ t

/-- The physical index-weighted Krylov complexity is the three-atom formula. -/
theorem complexity_eq_threeAtom (h : Data E A μ s) (t : ℝ) :
    chainComplexity E A (chain E A μ) t = Qubit.threeAtom μ t := by
  unfold chainComplexity
  simp only [probabilities h]
  simpa [Fin.sum_univ_succ, show (1 : ℝ) + 1 = 2 by norm_num] using Qubit.weighted_probabilities μ t

/-- A convenient bridge from the real-matrix spectral certificates. -/
theorem data_of_real {n : ℕ} (E : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (μ s : ℝ) (hs : 0 < s) (hm : 0 < μ) (hm' : μ < 1)
    (hB : ∀ i j, B i j ≠ 0 → E i - E j = -1 ∨ E i - E j = 0 ∨ E i - E j = 1)
    (hw : ∀ k : Fin 3,
      States.operatorGapWeight E B (FamilyStates.threeNodes k) / s =
        (![μ/2,1-μ,μ/2] : Fin 3 → ℝ) k) :
    Data E (B.map Complex.ofReal) μ s := by
  refine ⟨hs, hm, hm', ?_, ?_, ?_, ?_⟩
  · intro i j hn
    apply hB i j
    simpa using hn
  all_goals rw [real_gapWeight]
  · have hh := hw 0
    change States.operatorGapWeight E B (-1) / s = μ/2 at hh
    have hh' := (div_eq_iff hs.ne').mp hh
    linarith
  · have hh := hw 1
    change States.operatorGapWeight E B 0 / s = 1-μ at hh
    have hh' := (div_eq_iff hs.ne').mp hh
    linarith
  · have hh := hw 2
    change States.operatorGapWeight E B 1 / s = μ/2 at hh
    have hh' := (div_eq_iff hs.ne').mp hh
    linarith

open FamilyStates Ratios

theorem qutritRoot_data {m : ℝ} (hm : 4 ≤ m) :
    Data qutritEnergy ((qutritRoot m).map Complex.ofReal) (qutritWeightS (m^2)) 1 := by
  have hz : 16 ≤ m^2 := by nlinarith
  have hw := qutrit_weights hz
  apply data_of_real _ _ _ _ (by norm_num) (by linarith [hw.1,hw.2.1])
    (by linarith [hw.2.2.2])
  · intro i j hn
    fin_cases i <;> fin_cases j <;>
      norm_num [qutritRoot, qutritEnergy] at hn ⊢
  · intro k
    simpa using qutritRoot_gap_weights m k

theorem qutritState_data {m : ℝ} (hm : 4 ≤ m) :
    Data qutritEnergy ((qutritState m).map Complex.ofReal) (qutritWeightK (m^2))
      (trace (qutritState m * qutritState m)) := by
  have hz : 16 ≤ m^2 := by nlinarith
  have hw := qutrit_weights hz
  have hs : 0 < trace (qutritState m * qutritState m) := by
    rw [qutritState_purity]; positivity
  apply data_of_real _ _ _ _ hs hw.1 (by linarith [hw.2.1, hw.2.2.2])
  · intro i j hn
    fin_cases i <;> fin_cases j <;>
      norm_num [qutritState, qutritRaw, qutritEnergy] at hn ⊢
  · exact qutritState_gap_weights m

theorem fixedRoot_data {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) :
    Data fixedEnergy ((fixedRoot ε).map Complex.ofReal) (ε/10) 1 := by
  apply data_of_real _ _ _ _ (by norm_num) (by positivity) (by linarith)
  · intro i j hn
    fin_cases i <;> fin_cases j <;>
      norm_num [fixedRoot, fixedEnergy] at hn ⊢
  · intro k
    have hw := fixedRoot_gap_weights he he' k
    fin_cases k <;> norm_num at hw ⊢ <;> linarith

theorem fixedState_data {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) :
    Data fixedEnergy ((fixedState ε).map Complex.ofReal) (9*ε^2/25) (1/2) := by
  have hm : 9*ε^2/25 < 1 := by nlinarith [mul_pos he (sub_pos.mpr he')]
  apply data_of_real _ _ _ _ (by norm_num) (by positivity) hm
  · intro i j hn
    fin_cases i <;> fin_cases j <;>
      norm_num [fixedState, fixedEnergy] at hn ⊢
  · intro k
    have hw := fixedState_gap_weights he he' k
    rw [fixedState_purity he he'] at hw
    fin_cases k <;> norm_num at hw ⊢ <;> linarith

/-- Qutrit spread: actual unitary evolution of the canonical positive root. -/
def qutritSpread (m t : ℝ) : ℝ :=
  let A := (qutritRoot m).map Complex.ofReal
  chainComplexity qutritEnergy A (chain qutritEnergy A (qutritWeightS (m^2))) t

/-- Qutrit mixed-operator complexity: actual density-matrix seed. -/
def qutritMixed (m t : ℝ) : ℝ :=
  let A := (qutritState m).map Complex.ofReal
  chainComplexity qutritEnergy A (chain qutritEnergy A (qutritWeightK (m^2))) t

def fixedSpread (ε t : ℝ) : ℝ :=
  let A := (fixedRoot ε).map Complex.ofReal
  chainComplexity fixedEnergy A (chain fixedEnergy A (ε/10)) t

def fixedMixed (ε t : ℝ) : ℝ :=
  let A := (fixedState ε).map Complex.ofReal
  chainComplexity fixedEnergy A (chain fixedEnergy A (9*ε^2/25)) t

theorem qutritSpread_eq {m : ℝ} (hm : 4 ≤ m) (t : ℝ) :
    qutritSpread m t = Qubit.threeAtom (qutritWeightS (m^2)) t :=
  complexity_eq_threeAtom (qutritRoot_data hm) t

theorem qutritMixed_eq {m : ℝ} (hm : 4 ≤ m) (t : ℝ) :
    qutritMixed m t = Qubit.threeAtom (qutritWeightK (m^2)) t :=
  complexity_eq_threeAtom (qutritState_data hm) t

theorem fixedSpread_eq {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) (t : ℝ) :
    fixedSpread ε t = Qubit.threeAtom (ε/10) t :=
  complexity_eq_threeAtom (fixedRoot_data he he') t

theorem fixedMixed_eq {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) (t : ℝ) :
    fixedMixed ε t = Qubit.threeAtom (9*ε^2/25) t :=
  complexity_eq_threeAtom (fixedState_data he he') t

/-- No universal positive multiplier exists for the actual qutrit operator
chains. Both seeds are the certified density matrix and its positive root. -/
theorem qutrit_operator_no_positive_multiplier :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, 4 ≤ m →
      c * qutritSpread m Real.pi ≤ qutritMixed m Real.pi := by
  rintro ⟨c, hc, hall⟩
  apply qutrit_no_positive_multiplier
  refine ⟨c, hc, ?_⟩
  intro m hm
  have hh := hall m hm
  rw [qutritSpread_eq hm, qutritMixed_eq hm,
    threeAtom_time_eq, threeAtom_time_eq] at hh
  simpa only [Real.sin_pi_div_two, one_pow] using hh

/-- Exact fixed-purity quotient of the actual physical operator chains. -/
theorem fixed_operator_quotient {ε t : ℝ} (he : 0 < ε) (he' : ε < 5/18)
    (ht : Real.sin (t/2) ≠ 0) :
    fixedSpread ε t / fixedMixed ε t = fixedPurityRatio ε (Real.sin (t/2)^2) := by
  rw [fixedSpread_eq he he', fixedMixed_eq he he', threeAtom_time_eq, threeAtom_time_eq]
  exact fixedPurity_spectral_quotient he he' (sq_pos_of_ne_zero ht)

/-- Uniform unboundedness for genuine operator Krylov complexities, with
full-rank, unit-trace, exactly fixed-purity physical witnesses. -/
theorem fixed_operator_uniform_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 5/18 ∧ (fixedState ε).PosDef ∧
      trace (fixedState ε) = 1 ∧ trace (fixedState ε * fixedState ε) = 1/2 ∧
      ∀ t : ℝ, Real.sin (t/2) ≠ 0 → M < fixedSpread ε t / fixedMixed ε t := by
  obtain ⟨ε, he, he', hh⟩ := fixedPurity_uniform_unbounded M
  refine ⟨ε, he, he', fixedState_posDef he he', fixedState_trace ε,
    fixedState_purity he he', ?_⟩
  intro t ht
  rw [fixed_operator_quotient he he' ht]
  exact hh _ (sq_nonneg _) (Real.sin_sq_le_one _)

end Krylov.ThreeAtomOperator
