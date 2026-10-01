import Krylov.OperatorBridge
import Krylov.Evolution

/-!
Explicit operator Krylov chains and their normalized probabilities.  Vectors
are kept orthogonal rather than rescaled by square roots: `chainProbability`
divides by both the squared norm of the seed and the squared norm of the
chain vector, exactly as for the corresponding unit vectors.
-/
namespace Krylov.ConcreteChains
open Matrix OperatorBridge
open scoped BigOperators
noncomputable section

/-- Squared amplitude using an unnormalized seed and orthogonal chain vector. -/
def chainProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (A v : Operator ι) (t : ℝ) : ℝ :=
  Complex.normSq (hsInner v (diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ)) /
    ((hsInner A A).re * (hsInner v v).re)

def chainComplexity {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (E : ι → ℝ) (A : Operator ι) (v : Fin m → Operator ι) (t : ℝ) : ℝ :=
  ∑ k, (k.val : ℝ) * chainProbability E A (v k) t

theorem hsInner_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Operator ι) (c d : ℂ) :
    hsInner (c • A) (d • B) = star c * d * hsInner A B := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    Complex.star_def, map_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem hsInner_self_real {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Operator ι) :
    hsInner A A = ((hsInner A A).re : ℂ) := by
  have h : hsInner A A = ((∑ i, ∑ j, Complex.normSq (A i j) : ℝ) : ℂ) := by
    simp [hsInner, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  rw [h]; simp

def normalized {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Operator ι) : Operator ι :=
  ((Real.sqrt (hsInner A A).re)⁻¹ : ℂ) • A

theorem normalized_unit {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Operator ι)
    (hA : 0 < (hsInner A A).re) : hsInner (normalized A) (normalized A) = 1 := by
  rw [normalized, hsInner_smul, hsInner_self_real A]
  have hs : Real.sqrt (hsInner A A).re ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hsq := Real.sq_sqrt hA.le
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  field_simp

/-- The norm-divided probability is exactly the squared amplitude of the unit vectors. -/
theorem chainProbability_eq_normalized_amplitude {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (A v : Operator ι) (t : ℝ)
    (hA : 0 < (hsInner A A).re) (hv : 0 < (hsInner v v).re) :
    chainProbability E A v t = Complex.normSq
      (hsInner (normalized v) (diagonalUnitary E t * normalized A * (diagonalUnitary E t)ᴴ)) := by
  have hsa : Real.sqrt (hsInner A A).re ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hsv : Real.sqrt (hsInner v v).re ≠ 0 := (Real.sqrt_pos.2 hv).ne'
  have hqa := Real.sq_sqrt hA.le
  have hqv := Real.sq_sqrt hv.le
  simp only [normalized, Matrix.mul_smul, Matrix.smul_mul, hsInner_smul,
    map_mul, Complex.star_def, Complex.conj_ofReal, Complex.normSq_ofReal,
    Complex.normSq_inv]
  unfold chainProbability
  field_simp
  left; ring

def hsInnerLinearRight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Operator ι) : Operator ι →ₗ[ℂ] ℂ where
  toFun B := hsInner A B
  map_add' B C := by simp [hsInner, mul_add, Finset.sum_add_distrib]
  map_smul' c B := by
    simp only [hsInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring

/-- Orthogonal nonzero operator vectors form a linearly independent chain. -/
theorem linearIndependent_of_hsGram {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (v : κ → Operator ι) (d : κ → ℂ)
    (hg : ∀ k l, hsInner (v k) (v l) = if k = l then d k else 0)
    (hd : ∀ k, d k ≠ 0) : LinearIndependent ℂ v := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc k
  have he := congrArg (hsInnerLinearRight (v k)) hc
  simp only [map_sum, map_smul, map_zero] at he
  change (∑ l, c l * hsInner (v k) (v l)) = 0 at he
  simp only [hg, mul_ite, mul_zero] at he
  rw [Finset.sum_ite_eq] at he
  simp only [Finset.mem_univ, ↓reduceIte] at he
  exact (mul_eq_zero.mp he).resolve_right (hd k)

/-- The cyclic Krylov subspace of a linear generator and seed. -/
def cyclicSpan {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : Module.End ℂ M) (A : M) : Submodule ℂ M :=
  Submodule.span ℂ (Set.range (fun k : ℕ => (L^k) A))

theorem polynomial_mem_cyclicSpan {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : Module.End ℂ M) (A : M) (p : Polynomial ℂ) :
    (Polynomial.aeval L) p A ∈ cyclicSpan L A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, LinearMap.add_apply] using (cyclicSpan L A).add_mem hp hq
  | monomial k a =>
    have hk : (L^k) A ∈ cyclicSpan L A := Submodule.subset_span ⟨k, rfl⟩
    simpa [Polynomial.aeval_monomial, Module.End.mul_apply] using
      (cyclicSpan L A).smul_mem a hk

theorem cyclicSpan_le_of_invariant {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : Module.End ℂ M) (A : M) (W : Submodule ℂ M) (hA : A ∈ W)
    (hL : ∀ x ∈ W, L x ∈ W) : cyclicSpan L A ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  induction k with
  | zero => simpa using hA
  | succ k ih => simpa only [pow_succ', Module.End.mul_apply] using hL _ ih

theorem span_range_invariant {κ M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : Module.End ℂ M) (v : κ → M)
    (hv : ∀ k, L (v k) ∈ Submodule.span ℂ (Set.range v)) :
    ∀ x ∈ Submodule.span ℂ (Set.range v), L x ∈ Submodule.span ℂ (Set.range v) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨k,rfl⟩ := hy; exact hv k
  | zero => simpa using (Submodule.span ℂ (Set.range v)).zero_mem
  | add x y hx hy hpx hpy =>
    simpa only [map_add] using (Submodule.span ℂ (Set.range v)).add_mem hpx hpy
  | smul a x hx hpx =>
    simpa only [map_smul] using (Submodule.span ℂ (Set.range v)).smul_mem a hpx

/-- Polynomial membership plus an invariant chain containing the seed proves completeness. -/
theorem span_polynomial_chain_eq_cyclic {κ M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : Module.End ℂ M) (A : M) (v : κ → M) (p : κ → Polynomial ℂ)
    (hp : ∀ k, v k = (Polynomial.aeval L) (p k) A)
    (hA : A ∈ Submodule.span ℂ (Set.range v))
    (hL : ∀ k, L (v k) ∈ Submodule.span ℂ (Set.range v)) :
    Submodule.span ℂ (Set.range v) = cyclicSpan L A := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    rw [hp]; exact polynomial_mem_cyclicSpan L A (p k)
  · exact cyclicSpan_le_of_invariant L A _ hA (span_range_invariant L v hL)

namespace RightMixed

def seed : Operator (Fin 3) := States.rhoRE.map Complex.ofReal

def polynomial : Fin 3 → Polynomial ℂ :=
  ![1, Polynomial.X, Polynomial.X ^ 2 - Polynomial.C (225/169)]

def chain (k : Fin 3) : Operator (Fin 3) :=
  (Polynomial.aeval (liouvillian States.energyR)) (polynomial k) seed

theorem chain_entry (k i j : Fin 3) :
    chain k i j =
      (polynomial k).eval ((States.energyR i - States.energyR j : ℝ) : ℂ) * seed i j :=
  polynomial_liouvillian_entry _ _ _ _ _

theorem chain_zero : chain 0 = seed := by
  ext i j; simp [chain_entry, polynomial]

theorem gram : ∀ k l,
    hsInner (chain k) (chain l) =
      if k = l then ((1/2 : ℝ) * (Spectral.RightMixed.norms k : ℝ) : ℂ) else 0 := by
  intro k l
  fin_cases k <;> fin_cases l <;>
    norm_num [hsInner, chain_entry, polynomial, seed, States.rhoRE, States.energyR,
      Spectral.RightMixed.norms, Fin.sum_univ_succ, Complex.star_def]

theorem ordered_recurrence : ∀ k,
    liouvillian States.energyR (chain k) =
      (if h : k.val + 1 < 3 then chain ⟨k.val + 1,h⟩ else 0) +
      (if h : 0 < k.val then
        (Spectral.RightMixed.bSquared k : ℂ) • chain ⟨k.val - 1, by omega⟩ else 0) := by
  intro k; ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [liouvillian, chain_entry, polynomial, seed, States.rhoRE, States.energyR,
      Spectral.RightMixed.bSquared]

theorem evolved_amplitude (k : Fin 3) (t : ℝ) :
    hsInner (chain k) (diagonalUnitary States.energyR t * seed *
      (diagonalUnitary States.energyR t)ᴴ) =
      (1/2 : ℂ) * Spectral.spectralAmplitude Spectral.RightMixed.nodes
        Spectral.RightMixed.weights (Spectral.RightMixed.polys k) t := by
  rw [diagonalUnitary_conjugation]
  fin_cases k <;>
    norm_num [hsInner, chain_entry, spectralFilter, polynomial, seed,
      States.rhoRE, States.energyR, Spectral.spectralAmplitude,
      Spectral.RightMixed.nodes, Spectral.RightMixed.weights, Spectral.RightMixed.polys,
      Fin.sum_univ_succ, Complex.star_def, phase] <;> ring

theorem seed_norm : hsInner seed seed = (1/2 : ℂ) := by
  norm_num [hsInner, seed, States.rhoRE, Fin.sum_univ_succ, Complex.star_def]

theorem probability_eq_spectral (k : Fin 3) (t : ℝ) :
    chainProbability States.energyR seed (chain k) t =
      Spectral.timeProbability Spectral.RightMixed.nodes Spectral.RightMixed.weights
        (Spectral.RightMixed.polys k) t := by
  rw [chainProbability, evolved_amplitude, seed_norm, gram]
  simp only [↓reduceIte, map_mul, Complex.normSq_ofReal]
  rw [Spectral.timeProbability_eq_exp_norm]
  have hg := Spectral.RightMixed.gram k k
  simp only [↓reduceIte] at hg
  rw [hg]
  fin_cases k <;> norm_num [Spectral.RightMixed.norms] <;> ring

theorem exact_probabilities (k : Fin 3) :
    chainProbability States.energyR seed (chain k) (Real.pi/3) =
      (Spectral.RightMixed.probabilities k : ℝ) := by
  rw [probability_eq_spectral, Spectral.RightMixed.time_probabilities]

theorem exact_complexity :
    chainComplexity States.energyR seed chain (Real.pi/3) = 1141425/913952 := by
  unfold chainComplexity
  simp only [exact_probabilities]
  norm_num [Spectral.RightMixed.probabilities, Fin.sum_univ_succ]

theorem chain_norm_pos (k : Fin 3) : 0 < (hsInner (chain k) (chain k)).re := by
  rw [gram]; simp only [↓reduceIte]
  fin_cases k <;> norm_num [Spectral.RightMixed.norms]

theorem chain_nonzero (k : Fin 3) : chain k ≠ 0 := by
  intro hz
  have hp := chain_norm_pos k
  simp [hz, hsInner] at hp

theorem normalized_chain_orthonormal : ∀ k l,
    hsInner (normalized (chain k)) (normalized (chain l)) = if k = l then 1 else 0 := by
  intro k l
  by_cases h : k = l
  · subst l; simp only [↓reduceIte]
    exact normalized_unit (chain k) (chain_norm_pos k)
  · simp [normalized, hsInner_smul, gram, h]

theorem chain_linearIndependent : LinearIndependent ℂ chain := by
  apply linearIndependent_of_hsGram chain
    (fun k => ((1/2 : ℝ) * (Spectral.RightMixed.norms k : ℝ) : ℂ)) gram
  intro k; fin_cases k <;> norm_num [Spectral.RightMixed.norms]

theorem normalized_chain_linearIndependent : LinearIndependent ℂ (fun k => normalized (chain k)) := by
  exact linearIndependent_of_hsGram _ (fun _ => 1) normalized_chain_orthonormal (by simp)

theorem chain_spans_cyclic :
    Submodule.span ℂ (Set.range chain) = cyclicSpan (liouvillian States.energyR) seed := by
  apply span_polynomial_chain_eq_cyclic (liouvillian States.energyR) seed chain polynomial
  · intro k; rfl
  · rw [← chain_zero]; exact Submodule.subset_span ⟨0, rfl⟩
  · intro k
    rw [ordered_recurrence]
    apply Submodule.add_mem
    · split_ifs with h
      · exact Submodule.subset_span ⟨_, rfl⟩
      · exact Submodule.zero_mem _
    · split_ifs with h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · exact Submodule.zero_mem _

theorem cyclic_dimension :
    Module.finrank ℂ (cyclicSpan (liouvillian States.energyR) seed) = 3 := by
  rw [← chain_spans_cyclic]
  simpa using finrank_span_eq_card chain_linearIndependent

end RightMixed

namespace LeftMixed

def seed : Operator (Fin 3) := States.rhoL.map Complex.ofReal

def polynomial : Fin 3 → Polynomial ℂ :=
  ![1, Polynomial.X, Polynomial.X ^ 2 - Polynomial.C (3/182)]

def chain (k : Fin 3) : Operator (Fin 3) :=
  (Polynomial.aeval (liouvillian States.energyL)) (polynomial k) seed

theorem chain_entry (k i j : Fin 3) :
    chain k i j =
      (polynomial k).eval ((States.energyL i - States.energyL j : ℝ) : ℂ) * seed i j :=
  polynomial_liouvillian_entry _ _ _ _ _

theorem chain_zero : chain 0 = seed := by
  ext i j; simp [chain_entry, polynomial]

theorem gram : ∀ k l,
    hsInner (chain k) (chain l) =
      if k = l then ((13/21 : ℝ) * (Spectral.LeftMixed.norms k : ℝ) : ℂ) else 0 := by
  intro k l
  fin_cases k <;> fin_cases l <;>
    norm_num [hsInner, chain_entry, polynomial, seed, States.rhoL, States.energyL,
      Spectral.LeftMixed.norms, Fin.sum_univ_succ, Complex.star_def]

theorem ordered_recurrence : ∀ k,
    liouvillian States.energyL (chain k) =
      (if h : k.val + 1 < 3 then chain ⟨k.val + 1,h⟩ else 0) +
      (if h : 0 < k.val then
        (Spectral.LeftMixed.bSquared k : ℂ) • chain ⟨k.val - 1, by omega⟩ else 0) := by
  intro k; ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [liouvillian, chain_entry, polynomial, seed, States.rhoL, States.energyL,
      Spectral.LeftMixed.bSquared]

theorem evolved_amplitude (k : Fin 3) (t : ℝ) :
    hsInner (chain k) (diagonalUnitary States.energyL t * seed *
      (diagonalUnitary States.energyL t)ᴴ) =
      (13/21 : ℂ) * Spectral.spectralAmplitude Spectral.LeftMixed.nodes
        Spectral.LeftMixed.weights (Spectral.LeftMixed.polys k) t := by
  rw [diagonalUnitary_conjugation]
  fin_cases k <;>
    norm_num [hsInner, chain_entry, spectralFilter, polynomial, seed,
      States.rhoL, States.energyL, Spectral.spectralAmplitude,
      Spectral.LeftMixed.nodes, Spectral.LeftMixed.weights, Spectral.LeftMixed.polys,
      Fin.sum_univ_succ, Complex.star_def, phase] <;> ring

theorem seed_norm : hsInner seed seed = (13/21 : ℂ) := by
  norm_num [hsInner, seed, States.rhoL, Fin.sum_univ_succ, Complex.star_def]

theorem probability_eq_spectral (k : Fin 3) (t : ℝ) :
    chainProbability States.energyL seed (chain k) t =
      Spectral.timeProbability Spectral.LeftMixed.nodes Spectral.LeftMixed.weights
        (Spectral.LeftMixed.polys k) t := by
  rw [chainProbability, evolved_amplitude, seed_norm, gram]
  simp only [↓reduceIte, map_mul, Complex.normSq_ofReal]
  rw [Spectral.timeProbability_eq_exp_norm]
  have hg := Spectral.LeftMixed.gram k k
  simp only [↓reduceIte] at hg
  rw [hg]
  fin_cases k <;> norm_num [Spectral.LeftMixed.norms] <;> ring

theorem exact_probabilities (k : Fin 3) :
    chainProbability States.energyL seed (chain k) (Real.pi) =
      (Spectral.LeftMixed.probabilities k : ℝ) := by
  rw [probability_eq_spectral, Spectral.LeftMixed.time_probabilities]

theorem exact_complexity :
    chainComplexity States.energyL seed chain (Real.pi) = 1074/8281 := by
  unfold chainComplexity
  simp only [exact_probabilities]
  norm_num [Spectral.LeftMixed.probabilities, Fin.sum_univ_succ]

theorem chain_norm_pos (k : Fin 3) : 0 < (hsInner (chain k) (chain k)).re := by
  rw [gram]; simp only [↓reduceIte]
  fin_cases k <;> norm_num [Spectral.LeftMixed.norms]

theorem chain_nonzero (k : Fin 3) : chain k ≠ 0 := by
  intro hz
  have hp := chain_norm_pos k
  simp [hz, hsInner] at hp

theorem normalized_chain_orthonormal : ∀ k l,
    hsInner (normalized (chain k)) (normalized (chain l)) = if k = l then 1 else 0 := by
  intro k l
  by_cases h : k = l
  · subst l; simp only [↓reduceIte]
    exact normalized_unit (chain k) (chain_norm_pos k)
  · simp [normalized, hsInner_smul, gram, h]

theorem chain_linearIndependent : LinearIndependent ℂ chain := by
  apply linearIndependent_of_hsGram chain
    (fun k => ((13/21 : ℝ) * (Spectral.LeftMixed.norms k : ℝ) : ℂ)) gram
  intro k; fin_cases k <;> norm_num [Spectral.LeftMixed.norms]

theorem normalized_chain_linearIndependent : LinearIndependent ℂ (fun k => normalized (chain k)) := by
  exact linearIndependent_of_hsGram _ (fun _ => 1) normalized_chain_orthonormal (by simp)

theorem chain_spans_cyclic :
    Submodule.span ℂ (Set.range chain) = cyclicSpan (liouvillian States.energyL) seed := by
  apply span_polynomial_chain_eq_cyclic (liouvillian States.energyL) seed chain polynomial
  · intro k; rfl
  · rw [← chain_zero]; exact Submodule.subset_span ⟨0, rfl⟩
  · intro k
    rw [ordered_recurrence]
    apply Submodule.add_mem
    · split_ifs with h
      · exact Submodule.subset_span ⟨_, rfl⟩
      · exact Submodule.zero_mem _
    · split_ifs with h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · exact Submodule.zero_mem _

theorem cyclic_dimension :
    Module.finrank ℂ (cyclicSpan (liouvillian States.energyL) seed) = 3 := by
  rw [← chain_spans_cyclic]
  simpa using finrank_span_eq_card chain_linearIndependent

end LeftMixed

namespace LeftSpread

private theorem csL_sq : (States.sL : ℂ)^2 = 1/84 := by
  rw [← Complex.ofReal_pow, States.sL_sq]; norm_num

def seed : Operator (Fin 3) := States.rootL.map Complex.ofReal

def polynomial : Fin 3 → Polynomial ℂ :=
  ![1, Polynomial.X, Polynomial.X ^ 2 - Polynomial.C (1/42)]

def chain (k : Fin 3) : Operator (Fin 3) :=
  (Polynomial.aeval (liouvillian States.energyL)) (polynomial k) seed

theorem chain_entry (k i j : Fin 3) :
    chain k i j =
      (polynomial k).eval ((States.energyL i - States.energyL j : ℝ) : ℂ) * seed i j :=
  polynomial_liouvillian_entry _ _ _ _ _

theorem chain_zero : chain 0 = seed := by
  ext i j; simp [chain_entry, polynomial]

theorem gram : ∀ k l,
    hsInner (chain k) (chain l) =
      if k = l then ((1 : ℝ) * (Spectral.LeftSpread.norms k : ℝ) : ℂ) else 0 := by
  intro k l
  fin_cases k <;> fin_cases l <;>
    norm_num [hsInner, chain_entry, polynomial, seed, States.rootL, States.energyL,
      Spectral.LeftSpread.norms, Fin.sum_univ_succ, Complex.star_def] <;> ring_nf <;> norm_num [csL_sq]

theorem ordered_recurrence : ∀ k,
    liouvillian States.energyL (chain k) =
      (if h : k.val + 1 < 3 then chain ⟨k.val + 1,h⟩ else 0) +
      (if h : 0 < k.val then
        (Spectral.LeftSpread.bSquared k : ℂ) • chain ⟨k.val - 1, by omega⟩ else 0) := by
  intro k; ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [liouvillian, chain_entry, polynomial, seed, States.rootL, States.energyL,
      Spectral.LeftSpread.bSquared] <;> ring

theorem evolved_amplitude (k : Fin 3) (t : ℝ) :
    hsInner (chain k) (diagonalUnitary States.energyL t * seed *
      (diagonalUnitary States.energyL t)ᴴ) =
      (1 : ℂ) * Spectral.spectralAmplitude Spectral.LeftSpread.nodes
        Spectral.LeftSpread.weights (Spectral.LeftSpread.polys k) t := by
  rw [diagonalUnitary_conjugation]
  fin_cases k <;>
    norm_num [hsInner, chain_entry, spectralFilter, polynomial, seed,
      States.rootL, States.energyL, Spectral.spectralAmplitude,
      Spectral.LeftSpread.nodes, Spectral.LeftSpread.weights, Spectral.LeftSpread.polys,
      Fin.sum_univ_succ, Complex.star_def, phase] <;> ring_nf <;> norm_num [csL_sq] <;> ring

theorem seed_norm : hsInner seed seed = (1 : ℂ) := by
  norm_num [hsInner, seed, States.rootL, Fin.sum_univ_succ, Complex.star_def] <;> ring_nf <;> norm_num [csL_sq]

theorem probability_eq_spectral (k : Fin 3) (t : ℝ) :
    chainProbability States.energyL seed (chain k) t =
      Spectral.timeProbability Spectral.LeftSpread.nodes Spectral.LeftSpread.weights
        (Spectral.LeftSpread.polys k) t := by
  rw [chainProbability, evolved_amplitude, seed_norm, gram]
  simp only [↓reduceIte, map_mul, Complex.normSq_ofReal]
  rw [Spectral.timeProbability_eq_exp_norm]
  have hg := Spectral.LeftSpread.gram k k
  simp only [↓reduceIte] at hg
  rw [hg]
  fin_cases k <;> norm_num [Spectral.LeftSpread.norms] <;> ring

theorem exact_probabilities (k : Fin 3) :
    chainProbability States.energyL seed (chain k) (Real.pi) =
      (Spectral.LeftSpread.probabilities k : ℝ) := by
  rw [probability_eq_spectral, Spectral.LeftSpread.time_probabilities]

theorem exact_complexity :
    chainComplexity States.energyL seed chain (Real.pi) = 82/441 := by
  unfold chainComplexity
  simp only [exact_probabilities]
  norm_num [Spectral.LeftSpread.probabilities, Fin.sum_univ_succ]

theorem chain_norm_pos (k : Fin 3) : 0 < (hsInner (chain k) (chain k)).re := by
  rw [gram]; simp only [↓reduceIte]
  fin_cases k <;> norm_num [Spectral.LeftSpread.norms]

theorem chain_nonzero (k : Fin 3) : chain k ≠ 0 := by
  intro hz
  have hp := chain_norm_pos k
  simp [hz, hsInner] at hp

theorem normalized_chain_orthonormal : ∀ k l,
    hsInner (normalized (chain k)) (normalized (chain l)) = if k = l then 1 else 0 := by
  intro k l
  by_cases h : k = l
  · subst l; simp only [↓reduceIte]
    exact normalized_unit (chain k) (chain_norm_pos k)
  · simp [normalized, hsInner_smul, gram, h]

theorem chain_linearIndependent : LinearIndependent ℂ chain := by
  apply linearIndependent_of_hsGram chain
    (fun k => ((1 : ℝ) * (Spectral.LeftSpread.norms k : ℝ) : ℂ)) gram
  intro k; fin_cases k <;> norm_num [Spectral.LeftSpread.norms]

theorem normalized_chain_linearIndependent : LinearIndependent ℂ (fun k => normalized (chain k)) := by
  exact linearIndependent_of_hsGram _ (fun _ => 1) normalized_chain_orthonormal (by simp)

theorem chain_spans_cyclic :
    Submodule.span ℂ (Set.range chain) = cyclicSpan (liouvillian States.energyL) seed := by
  apply span_polynomial_chain_eq_cyclic (liouvillian States.energyL) seed chain polynomial
  · intro k; rfl
  · rw [← chain_zero]; exact Submodule.subset_span ⟨0, rfl⟩
  · intro k
    rw [ordered_recurrence]
    apply Submodule.add_mem
    · split_ifs with h
      · exact Submodule.subset_span ⟨_, rfl⟩
      · exact Submodule.zero_mem _
    · split_ifs with h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · exact Submodule.zero_mem _

theorem cyclic_dimension :
    Module.finrank ℂ (cyclicSpan (liouvillian States.energyL) seed) = 3 := by
  rw [← chain_spans_cyclic]
  simpa using finrank_span_eq_card chain_linearIndependent

end LeftSpread
theorem left_operator_violation :
    chainComplexity States.energyL LeftMixed.seed LeftMixed.chain Real.pi <
      chainComplexity States.energyL LeftSpread.seed LeftSpread.chain Real.pi := by
  rw [LeftMixed.exact_complexity, LeftSpread.exact_complexity]
  norm_num

theorem left_operator_gap :
    chainComplexity States.energyL LeftSpread.seed LeftSpread.chain Real.pi -
      chainComplexity States.energyL LeftMixed.seed LeftMixed.chain Real.pi = 4192/74529 := by
  rw [LeftMixed.exact_complexity, LeftSpread.exact_complexity]
  norm_num

end
end Krylov.ConcreteChains
