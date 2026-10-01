import Krylov.ThreeAtomOperator
import Krylov.FiniteOperator
import Krylov.Bounds

/-! Actual symmetric five-atom operator Krylov process. -/
noncomputable section
namespace Krylov.FiveAtom
open Matrix OperatorBridge ConcreteChains
open scoped BigOperators
set_option maxHeartbeats 4000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def zeroMass (u v : ℝ) := 1-u-v
def m2 (u v : ℝ) := u+4*v
def m4 (u v : ℝ) := u+16*v
def m6 (u v : ℝ) := u+64*v
def n2 (u v : ℝ) := m4 u v - m2 u v ^ 2
def alpha (u v : ℝ) := (m6 u v - m4 u v * m2 u v) / n2 u v
def beta (u v : ℝ) := alpha u v * m2 u v - m4 u v

def nodes : Fin 5 → ℝ := ![-2,-1,0,1,2]
def weights (u v : ℝ) : Fin 5 → ℝ := ![v/2,u/2,zeroMass u v,u/2,v/2]
def norms (u v : ℝ) : Fin 5 → ℝ :=
  ![1,m2 u v,n2 u v,36*u*v*m2 u v,144*zeroMass u v*u*v*n2 u v]
def polynomial (u v : ℝ) : Fin 5 → Polynomial ℂ :=
  ![1, Polynomial.X, Polynomial.X^2-Polynomial.C (m2 u v : ℂ),
    Polynomial.C (m2 u v : ℂ)*Polynomial.X^3-Polynomial.C (m4 u v : ℂ)*Polynomial.X,
    Polynomial.C (n2 u v : ℂ)*Polynomial.X^4-
      Polynomial.C ((m6 u v-m4 u v*m2 u v : ℝ) : ℂ)*Polynomial.X^2+
      Polynomial.C (((m6 u v-m4 u v*m2 u v)*m2 u v-m4 u v*n2 u v : ℝ) : ℂ)]
def chain (E : ι → ℝ) (A : Operator ι) (u v : ℝ) (k : Fin 5) : Operator ι :=
  (Polynomial.aeval (liouvillian E)) (polynomial u v k) A

structure Data (E : ι → ℝ) (A : Operator ι) (u v s : ℝ) : Prop where
  scale_pos : 0 < s
  mass_one_pos : 0 < u
  mass_two_pos : 0 < v
  mass_zero_pos : 0 < zeroMass u v
  support : ∀ i j, A i j ≠ 0 → E i - E j ∈ ({-2,-1,0,1,2} : Finset ℝ)
  gap_weights : ∀ k, gapWeight E A (nodes k) = s * weights u v k

variable {E : ι → ℝ} {A : Operator ι} {u v s : ℝ}

theorem m2_pos (h : Data E A u v s) : 0 < m2 u v := by
  have h1 := h.mass_one_pos; have h2 := h.mass_two_pos
  unfold m2; positivity

theorem n2_pos (h : Data E A u v s) : 0 < n2 u v := by
  have heq : n2 u v = zeroMass u v*u+16*zeroMass u v*v+9*u*v := by
    unfold n2 m2 m4 zeroMass; ring
  rw [heq]
  have h1 := h.mass_one_pos; have h2 := h.mass_two_pos; have h0 := h.mass_zero_pos
  positivity

theorem inner_filters (h : Data E A u v s) (f g : ℝ → ℂ) :
    hsInner (spectralFilter E f A) (spectralFilter E g A) =
      ∑ k, (s * weights u v k : ℝ) * star (f (nodes k)) * g (nodes k) := by
  rw [hsInner_filters_supported E f g A {-2,-1,0,1,2} h.support]
  have h0 := h.gap_weights 0
  have h1 := h.gap_weights 1
  have h2 := h.gap_weights 2
  have h3 := h.gap_weights 3
  have h4 := h.gap_weights 4
  change gapWeight E A (-2) = s * (v/2) at h0
  change gapWeight E A (-1) = s * (u/2) at h1
  change gapWeight E A 0 = s * zeroMass u v at h2
  change gapWeight E A 1 = s * (u/2) at h3
  change gapWeight E A 2 = s * (v/2) at h4
  norm_num [nodes, weights, Fin.sum_univ_succ,h0,h1,h2,h3,h4]

theorem chain_entry (E : ι → ℝ) (A : Operator ι) (u v : ℝ) (k : Fin 5) (i j : ι) :
    chain E A u v k i j = (polynomial u v k).eval ((E i-E j : ℝ) : ℂ) * A i j :=
  polynomial_liouvillian_entry _ _ _ _ _

theorem chain_zero (E : ι → ℝ) (A : Operator ι) (u v : ℝ) : chain E A u v 0 = A := by
  ext i j; simp [chain_entry,polynomial]

theorem gram (h : Data E A u v s) (k l : Fin 5) :
    hsInner (chain E A u v k) (chain E A u v l) =
      if k=l then ((s * norms u v k : ℝ) : ℂ) else 0 := by
  simp only [chain,polynomial_eq_spectralFilter]
  rw [inner_filters h]
  have hm : m2 u v ≠ 0 := (m2_pos h).ne'
  have hn : n2 u v ≠ 0 := (n2_pos h).ne'
  have hmc : (m2 u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
  have hnc : (n2 u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  fin_cases k <;> fin_cases l <;>
    norm_num [polynomial,weights,nodes,norms,Fin.sum_univ_succ,Complex.star_def,
      alpha,beta] <;>
    simp only [n2,m2,m4,m6,zeroMass,Complex.ofReal_sub,Complex.ofReal_add,
      Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_one,
      Complex.ofReal_ofNat] <;> ring

theorem seed_norm (h : Data E A u v s) : hsInner A A = (s : ℂ) := by
  have hh := gram h 0 0
  simpa [chain_zero,norms] using hh

theorem norms_pos (h : Data E A u v s) (k : Fin 5) : 0 < norms u v k := by
  have hm := m2_pos h; have hn := n2_pos h
  have h1 := h.mass_one_pos; have h2 := h.mass_two_pos; have h0 := h.mass_zero_pos
  fin_cases k <;> norm_num [norms] <;> positivity

theorem chain_norm_pos (h : Data E A u v s) (k : Fin 5) :
    0 < (hsInner (chain E A u v k) (chain E A u v k)).re := by
  rw [gram h]
  simp only [↓reduceIte,Complex.ofReal_re]
  exact mul_pos h.scale_pos (norms_pos h k)

theorem normalized_chain_orthonormal (h : Data E A u v s) (k l : Fin 5) :
    hsInner (normalized (chain E A u v k)) (normalized (chain E A u v l)) =
      if k=l then 1 else 0 := by
  by_cases he : k=l
  · subst l; simp only [↓reduceIte]
    exact normalized_unit _ (chain_norm_pos h k)
  · simp [normalized,hsInner_smul,gram h,he]

theorem chain_linearIndependent (h : Data E A u v s) :
    LinearIndependent ℂ (chain E A u v) := by
  apply linearIndependent_of_hsGram _ (fun k => ((s*norms u v k : ℝ) : ℂ)) (gram h)
  intro k
  exact Complex.ofReal_ne_zero.mpr (mul_pos h.scale_pos (norms_pos h k)).ne'

def forwardCoeff (u v : ℝ) : Fin 5 → ℝ := ![1,1,1/m2 u v,m2 u v/n2 u v,0]

def bSquared (u v : ℝ) : Fin 5 → ℝ :=
  ![0,m2 u v,n2 u v / m2 u v,36*u*v/n2 u v,
    4*zeroMass u v]

theorem ordered_recurrence (h : Data E A u v s) (k : Fin 5) :
    liouvillian E (chain E A u v k) =
      (if hk : k.val+1<5 then (forwardCoeff u v k : ℂ) • chain E A u v ⟨k.val+1,hk⟩ else 0) +
      (if hk : 0<k.val then
        (bSquared u v k : ℂ) • chain E A u v ⟨k.val-1,by omega⟩ else 0) := by
  have hm : m2 u v ≠ 0 := (m2_pos h).ne'
  have hn : n2 u v ≠ 0 := (n2_pos h).ne'
  have hmc : (m2 u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
  have hnc : (n2 u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  ext i j
  by_cases hz : A i j=0
  · fin_cases k <;> simp [liouvillian,chain_entry,polynomial,hz]
  · change ((E i-E j : ℝ) : ℂ) * chain E A u v k i j = _
    have hg := h.support i j hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with hg | hg | hg | hg | hg <;>
      rw [hg] <;> fin_cases k <;>
      simp [chain_entry,polynomial,bSquared,forwardCoeff,hg,alpha,beta] <;>
      (try field_simp [hmc,hnc]) <;>
      (try simp only [n2,m2,m4,m6,zeroMass,Complex.ofReal_sub,Complex.ofReal_add,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_one,Complex.ofReal_ofNat]) <;> ring

theorem chain_spans_cyclic (h : Data E A u v s) :
    Submodule.span ℂ (Set.range (chain E A u v)) = cyclicSpan (liouvillian E) A := by
  apply span_polynomial_chain_eq_cyclic (liouvillian E) A (chain E A u v) (polynomial u v)
  · intro k; rfl
  · exact Submodule.subset_span ⟨0,chain_zero E A u v⟩
  · intro k
    rw [ordered_recurrence h]
    apply Submodule.add_mem
    · split_ifs with hk
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,rfl⟩)
      · exact Submodule.zero_mem _
    · split_ifs with hk
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,rfl⟩)
      · exact Submodule.zero_mem _

theorem cyclic_dimension (h : Data E A u v s) :
    Module.finrank ℂ (cyclicSpan (liouvillian E) A) = 5 := by
  rw [← chain_spans_cyclic h]
  simpa using finrank_span_eq_card (chain_linearIndependent h)

private theorem nodes_injective : Function.Injective (fun k => (nodes k : ℂ)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [nodes] at hij ⊢

/-- Finite interpolation realizes the exponential orbit by a commutator polynomial. -/
theorem evolved_mem_cyclic (h : Data E A u v s) (t : ℝ) :
    diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ ∈ cyclicSpan (liouvillian E) A := by
  let p : Polynomial ℂ := Lagrange.interpolate Finset.univ
    (fun k => (nodes k : ℂ)) (fun k => phase (nodes k) t)
  have hp : ∀ k, p.eval (nodes k : ℂ) = phase (nodes k) t := by
    intro k
    exact Lagrange.eval_interpolate_at_node _ nodes_injective.injOn (Finset.mem_univ k)
  have heq : diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ =
      (Polynomial.aeval (liouvillian E)) p A := by
    rw [diagonalUnitary_conjugation]
    ext i j
    rw [polynomial_liouvillian_entry]
    by_cases hz : A i j=0
    · simp [spectralFilter,hz]
    · have hg := h.support i j hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hg
      have hex : ∃ k, E i-E j = nodes k := by
        rcases hg with hg | hg | hg | hg | hg
        · exact ⟨0,hg⟩
        · exact ⟨1,hg⟩
        · exact ⟨2,hg⟩
        · exact ⟨3,hg⟩
        · exact ⟨4,hg⟩
      obtain ⟨k,hk⟩ := hex
      simp only [spectralFilter,hk,hp]
  rw [heq]
  exact polynomial_mem_cyclicSpan _ _ p

theorem phase_normSq (ω t : ℝ) : Complex.normSq (phase ω t) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [phase,Complex.norm_exp]

theorem evolved_norm (h : Data E A u v s) (t : ℝ) :
    hsInner (diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ)
      (diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ) = (s : ℂ) := by
  simp only [diagonalUnitary_conjugation]
  rw [inner_filters h]
  simp only [mul_assoc,Complex.star_def,← Complex.normSq_eq_conj_mul_self,phase_normSq,
    Complex.ofReal_one,mul_one]
  norm_num [weights,Fin.sum_univ_succ,zeroMass]
  ring

theorem probabilities_sum (h : Data E A u v s) (t : ℝ) :
    ∑ k, chainProbability E A (chain E A u v k) t = 1 := by
  apply FiniteOperator.probability_sum E A _ (fun k => s*norms u v k) s t
    (gram h) (fun k => mul_pos h.scale_pos (norms_pos h k)) h.scale_pos
  · rw [seed_norm h]; rfl
  · rw [chain_spans_cyclic h]
    exact evolved_mem_cyclic h t
  · rw [evolved_norm h]; rfl

def returnAmplitude (u v t : ℝ) : ℝ :=
  zeroMass u v + u*Real.cos t + v*Real.cos (2*t)

theorem zero_amplitude (h : Data E A u v s) (t : ℝ) :
    hsInner (chain E A u v 0)
      (diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ) =
      (s * returnAmplitude u v t : ℝ) := by
  rw [chain,polynomial_eq_spectralFilter,diagonalUnitary_conjugation,inner_filters h]
  apply Complex.ext <;>
    simp [nodes,polynomial,weights,returnAmplitude,Fin.sum_univ_succ,phase,
      Complex.exp_re,Complex.exp_im,Complex.mul_re,Complex.mul_im,
      ← Complex.ofReal_cos,← Complex.ofReal_sin] <;>
    ring

theorem zero_probability (h : Data E A u v s) (t : ℝ) :
    chainProbability E A (chain E A u v 0) t = returnAmplitude u v t ^ 2 := by
  rw [chainProbability,zero_amplitude h,chain_zero,seed_norm h]
  simp only [Complex.normSq_ofReal,Complex.ofReal_re]
  field_simp [h.scale_pos.ne']
  ring

/-- Finite return bounds for this actual complete five-dimensional process. -/
theorem return_bounds (h : Data E A u v s) (t : ℝ) :
    1-returnAmplitude u v t^2 ≤ chainComplexity E A (chain E A u v) t ∧
      chainComplexity E A (chain E A u v) t ≤ 4*(1-returnAmplitude u v t^2) := by
  have hp : ∀ k, 0 ≤ chainProbability E A (chain E A u v k) t := by
    intro k
    unfold chainProbability
    exact div_nonneg (Complex.normSq_nonneg _) (mul_nonneg
      (by rw [seed_norm h]; exact h.scale_pos.le) (chain_norm_pos h k).le)
  have hh := finite_return_bounds 4 _ hp (probabilities_sum h t)
  simpa only [finiteComplexity,chainComplexity,zero_probability h,Nat.cast_ofNat] using hh

theorem loss_bounds (h : Data E A u v s) (t : ℝ)
    (h0 : 0 ≤ returnAmplitude u v t) (h1 : returnAmplitude u v t ≤ 1) :
    1-returnAmplitude u v t ≤ chainComplexity E A (chain E A u v) t ∧
      chainComplexity E A (chain E A u v) t ≤ 8*(1-returnAmplitude u v t) := by
  have hh := return_bounds h t
  have ha : returnAmplitude u v t^2 ≤ returnAmplitude u v t := by
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  constructor <;> nlinarith

end Krylov.FiveAtom
