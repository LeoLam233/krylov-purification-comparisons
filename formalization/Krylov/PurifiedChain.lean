import Krylov.ConcreteChains
import Krylov.Purification
import Krylov.OperatorBridge
import Krylov.Evolution

/-! The right witness's actual rank-one purified seed in an energy basis. -/
namespace Krylov.PurifiedChain
open Matrix OperatorBridge
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

abbrev Index := Fin 3 × Fin 3

def squareRootInEnergyBasis : Matrix (Fin 3) (Fin 3) ℂ :=
  (States.energyBasisRᵀ * States.rootR).map Complex.ofReal

def seed : Operator Index := Purification.pureSeed squareRootInEnergyBasis

def energies : Index → ℝ := fun a => States.energyR a.1

theorem row_weights : ∀ i,
    Purification.rowWeight squareRootInEnergyBasis i = States.rhoRE i i := by
  intro i; fin_cases i <;>
    norm_num [Purification.rowWeight, squareRootInEnergyBasis, States.energyBasisR,
      States.rootR, States.rhoRE, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.normSq_ofReal] <;> ring_nf <;>
    norm_num [States.q_sq, States.sR_sq]

theorem weights (ω : ℝ) :
    gapWeight energies seed ω =
      States.pureGapWeight States.energyR (fun i => States.rhoRE i i) ω := by
  change Purification.pureGapWeight States.energyR squareRootInEnergyBasis ω = _
  rw [Purification.pure_gap_difference_convolution]
  simp_rw [row_weights]
  rfl

theorem weights_certified : ∀ i : Fin 5,
    gapWeight energies seed (Spectral.RightPurified.nodes i : ℝ) =
      (Spectral.RightPurified.weights i : ℝ) := by
  intro i; rw [weights]; exact right_purified_weights_certified i


theorem energy_support : ∀ a b : Index,
    energies a - energies b ∈ ({-2,-1,0,1,2} : Finset ℝ) := by
  intro ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases k <;> norm_num [energies, States.energyR]

theorem grouped_inner (f g : ℝ → ℂ) :
    hsInner (spectralFilter energies f seed) (spectralFilter energies g seed) =
      ∑ k : Fin 5, (Spectral.RightPurified.weights k : ℂ) *
        star (f (Spectral.RightPurified.nodes k : ℝ)) *
        g (Spectral.RightPurified.nodes k : ℝ) := by
  rw [hsInner_filters_grouped energies f g seed {-2,-1,0,1,2} energy_support]
  simp_rw [weights]
  norm_num [States.pureGapWeight, States.gapWeight, States.energyR,
    States.rhoRE, Spectral.RightPurified.weights, Spectral.RightPurified.nodes,
    Fin.sum_univ_succ]


def polynomial : Fin 5 → Polynomial ℂ :=
  ![1, Polynomial.X,
    Polynomial.X^2 - Polynomial.C (17/13),
    Polynomial.X^3 - Polynomial.C (77/26)*Polynomial.X,
    Polynomial.X^4 - Polynomial.C (60944/14534)*Polynomial.X^2 + Polynomial.C (23409/14534)]

def chain (k : Fin 5) : Operator Index :=
  (Polynomial.aeval (liouvillian energies)) (polynomial k) seed

theorem chain_filter (k : Fin 5) :
    chain k = spectralFilter energies (fun x => (polynomial k).eval (x : ℂ)) seed :=
  polynomial_eq_spectralFilter energies _ _

theorem chain_zero : chain 0 = seed := by
  rw [chain_filter]; ext i j; simp [spectralFilter, polynomial]

theorem gram : ∀ k l,
    hsInner (chain k) (chain l) =
      if k=l then (Spectral.RightPurified.norms k : ℂ) else 0 := by
  intro k l; rw [chain_filter, chain_filter, grouped_inner]
  fin_cases k <;> fin_cases l <;>
    norm_num [polynomial, Spectral.RightPurified.norms, Spectral.RightPurified.nodes,
      Spectral.RightPurified.weights, Fin.sum_univ_succ, Complex.star_def]

theorem ordered_recurrence : ∀ k,
    liouvillian energies (chain k) =
      (if h : k.val+1 < 5 then chain ⟨k.val+1,h⟩ else 0) +
      (if h : 0<k.val then
        (Spectral.RightPurified.bSquared k : ℂ) • chain ⟨k.val-1,by omega⟩ else 0) := by
  intro k; ext ⟨i,j⟩ ⟨a,b⟩
  fin_cases k <;> fin_cases i <;> fin_cases a <;>
    simp [liouvillian, chain_filter, spectralFilter, polynomial, energies,
      States.energyR, Spectral.RightPurified.bSquared] <;> ring

theorem evolved_amplitude (k : Fin 5) (t : ℝ) :
    hsInner (chain k) (diagonalUnitary energies t * seed * (diagonalUnitary energies t)ᴴ) =
      Spectral.spectralAmplitude Spectral.RightPurified.nodes
        Spectral.RightPurified.weights (Spectral.RightPurified.polys k) t := by
  rw [chain_filter, diagonalUnitary_conjugation, grouped_inner]
  fin_cases k <;>
    norm_num [polynomial, Spectral.spectralAmplitude, phase,
      Spectral.RightPurified.nodes, Spectral.RightPurified.weights,
      Spectral.RightPurified.polys, Fin.sum_univ_succ, Complex.star_def]

theorem seed_norm : hsInner seed seed = 1 := by
  have h := gram 0 0
  simpa [chain_zero, Spectral.RightPurified.norms] using h

def chainProbability (k : Fin 5) (t : ℝ) : ℝ :=
  Complex.normSq (hsInner (chain k)
    (diagonalUnitary energies t * seed * (diagonalUnitary energies t)ᴴ)) /
    ((hsInner seed seed).re * (hsInner (chain k) (chain k)).re)

def complexity (t : ℝ) : ℝ := ∑ k : Fin 5, (k.val : ℝ) * chainProbability k t

theorem probability_eq_spectral (k : Fin 5) (t : ℝ) :
    chainProbability k t = Spectral.timeProbability Spectral.RightPurified.nodes
      Spectral.RightPurified.weights (Spectral.RightPurified.polys k) t := by
  rw [chainProbability, evolved_amplitude, seed_norm, gram]
  rw [Spectral.timeProbability_eq_exp_norm]
  have hn := Spectral.RightPurified.gram k k
  simp only [ite_true] at hn
  simp [hn]

theorem complexity_eq_spectral (t : ℝ) :
    complexity t = Spectral.timeComplexity Spectral.RightPurified.nodes
      Spectral.RightPurified.weights Spectral.RightPurified.polys t := by
  simp [complexity, Spectral.timeComplexity, probability_eq_spectral]

theorem exact_complexity : complexity (Real.pi/3) = 2967537/2456246 := by
  rw [complexity_eq_spectral, Spectral.RightPurified.time_complexity]


theorem chain_norm_positive (k : Fin 5) : 0 < (hsInner (chain k) (chain k)).re := by
  rw [gram]; simp only [ite_true, Complex.ratCast_re]
  exact_mod_cast Spectral.RightPurified.positive_norms k

theorem normalized_chain_orthonormal : ∀ k l,
    hsInner (ConcreteChains.normalized (chain k)) (ConcreteChains.normalized (chain l)) =
      if k=l then 1 else 0 := by
  intro k l
  by_cases h : k=l
  · subst l; simp [ConcreteChains.normalized_unit (chain k) (chain_norm_positive k)]
  · simp [ConcreteChains.normalized, ConcreteChains.hsInner_smul, gram, h]

theorem probability_normalized (k : Fin 5) (t : ℝ) :
    chainProbability k t = Complex.normSq
      (hsInner (ConcreteChains.normalized (chain k))
        (diagonalUnitary energies t * ConcreteChains.normalized seed *
          (diagonalUnitary energies t)ᴴ)) := by
  apply ConcreteChains.chainProbability_eq_normalized_amplitude
  · rw [seed_norm]; norm_num
  · exact chain_norm_positive k

theorem right_operator_gap :
    ConcreteChains.chainComplexity States.energyR ConcreteChains.RightMixed.seed
      ConcreteChains.RightMixed.chain (Real.pi/3) - complexity (Real.pi/3) =
    1600683/39299936 := by
  rw [ConcreteChains.RightMixed.exact_complexity, exact_complexity]; norm_num

theorem right_operator_violation :
    complexity (Real.pi/3) <
    ConcreteChains.chainComplexity States.energyR ConcreteChains.RightMixed.seed
      ConcreteChains.RightMixed.chain (Real.pi/3) := by
  have h := right_operator_gap
  linarith


theorem chain_linearIndependent : LinearIndependent ℂ chain := by
  apply ConcreteChains.linearIndependent_of_hsGram chain
    (fun k => (Spectral.RightPurified.norms k : ℂ)) gram
  intro k
  have hp := Spectral.RightPurified.positive_norms k
  exact_mod_cast ne_of_gt hp

theorem normalized_chain_linearIndependent :
    LinearIndependent ℂ (fun k => ConcreteChains.normalized (chain k)) := by
  exact ConcreteChains.linearIndependent_of_hsGram _ (fun _ => 1)
    normalized_chain_orthonormal (by simp)


theorem chain_spans_cyclic :
    Submodule.span ℂ (Set.range chain) = ConcreteChains.cyclicSpan (liouvillian energies) seed := by
  apply ConcreteChains.span_polynomial_chain_eq_cyclic (liouvillian energies) seed chain polynomial
  · intro k; rfl
  · rw [← chain_zero]; exact Submodule.subset_span ⟨0,rfl⟩
  · intro k
    rw [ordered_recurrence]
    apply Submodule.add_mem
    · split_ifs with h
      · exact Submodule.subset_span ⟨_,rfl⟩
      · exact Submodule.zero_mem _
    · split_ifs with h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,rfl⟩)
      · exact Submodule.zero_mem _

theorem cyclic_dimension :
    Module.finrank ℂ (ConcreteChains.cyclicSpan (liouvillian energies) seed) = 5 := by
  rw [← chain_spans_cyclic]
  simpa using finrank_span_eq_card chain_linearIndependent

end
end Krylov.PurifiedChain
