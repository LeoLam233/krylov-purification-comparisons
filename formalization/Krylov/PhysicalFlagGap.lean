import Krylov.FactorTwoTheorem

namespace Krylov.PhysicalFlagGap
open Matrix FactorTwoFinite
open scoped BigOperators InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cutoff (G : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℕ :=
  max ((Finset.univ.sup fun k : GSIndex (stateSequence G ψ) => k.val) * 2)
    (Finset.univ.sup fun k : GSIndex (operatorSequence G ψ) => k.val)

/-- Exact source eq:flag-gap, with genuine state/operator Gram–Schmidt flags.
The cutoff is derived from their finite supports, not an extra assumption. -/
theorem exact_gap (G : Matrix ι ι ℂ) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (hψ : ‖UnitaryEvolution.hilbertVector ψ‖ = 1) (t : ℝ) :
    let x := UnitaryEvolution.evolvedVector G ψ t
    complexity (operatorSequence G ψ) (FactorTwo.hilbertOuter x x) -
      2 * complexity (stateSequence G ψ) x =
      ∑ n ∈ Finset.range (cutoff G ψ),
        ‖((FactorTwo.hilbertTensorFlag G ψ n).orthogonalProjection
            (FactorTwo.hilbertOuter x x) : EuclideanSpace ℂ (ι × ι)) -
          ((FactorTwo.hilbertOperatorFlag G ψ n).orthogonalProjection
            (FactorTwo.hilbertOuter x x) : EuclideanSpace ℂ (ι × ι))‖ ^ 2 := by
  classical
  dsimp only
  let x := UnitaryEvolution.evolvedVector G ψ t
  have hunit : ‖x‖ = 1 := UnitaryEvolution.evolvedVector_unit G hG ψ hψ t
  have hp : (∑ k : GSIndex (stateSequence G ψ), probability (stateSequence G ψ) x k) = 1 := by
    rw [total_probability _ _ (FactorTwoTheorem.state_evolution_mem_cyclic G ψ t), hunit]
    norm_num
  have hq : (∑ k : GSIndex (operatorSequence G ψ),
      probability (operatorSequence G ψ) (FactorTwo.hilbertOuter x x) k) = 1 := by
    rw [total_probability _ _ (FactorTwoTheorem.pure_evolution_mem_cyclic G hG ψ t)]
    exact pure_norm_square_of_unit x hunit
  have hi : ∀ i ∈ (Finset.univ : Finset (GSIndex (stateSequence G ψ))),
      ∀ j ∈ (Finset.univ : Finset (GSIndex (stateSequence G ψ))),
      i.val + j.val ≤ cutoff G ψ := by
    intro i hi j hj
    unfold cutoff
    exact le_trans (by simpa [Nat.mul_two] using (Nat.add_le_add (Finset.le_sup hi) (Finset.le_sup hj))) (le_max_left _ _)
  have hj : ∀ k ∈ (Finset.univ : Finset (GSIndex (operatorSequence G ψ))),
      k.val ≤ cutoff G ψ := by
    intro k hk
    exact le_trans (Finset.le_sup hk) (le_max_right _ _)
  have hprod : (∑ p : GSIndex (stateSequence G ψ) × GSIndex (stateSequence G ψ),
      probability (stateSequence G ψ) x p.1 * probability (stateSequence G ψ) x p.2) = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hp, mul_one]
    exact hp
  apply Krylov.factor_two_gap_of_nested_projection_flags Finset.univ Finset.univ
    (fun k : GSIndex (stateSequence G ψ) => k.val)
    (fun k : GSIndex (operatorSequence G ψ) => k.val)
    (probability (stateSequence G ψ) x)
    (probability (operatorSequence G ψ) (FactorTwo.hilbertOuter x x))
    (cutoff G ψ) hp hi hj
    (FactorTwo.hilbertOperatorFlag G ψ) (FactorTwo.hilbertTensorFlag G ψ)
    (fun n _ => FactorTwo.hilbert_flag_inclusion G hG ψ n)
    (FactorTwo.hilbertOuter x x)
  · intro n _
    rw [actual_tensor_projection_mass]
    have ht := tail_complement
      (fun p : GSIndex (stateSequence G ψ) × GSIndex (stateSequence G ψ) => p.1.val+p.2.val)
      (fun p => probability (stateSequence G ψ) x p.1 * probability (stateSequence G ψ) x p.2)
      hprod n
    simpa only [Fintype.sum_prod_type, tensorIndices] using ht
  · intro n _
    rw [actual_operator_projection_mass]
    exact tail_complement _ _ hq n
end
end Krylov.PhysicalFlagGap
