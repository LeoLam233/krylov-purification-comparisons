import Krylov.FactorTwoFinite
import Krylov.CyclicEvolution
import Krylov.UnitaryEvolution

/-!
# The finite-dimensional physical factor-two theorem

The complexities below are the index-weighted squared amplitudes of the actual
normalized Gram-Schmidt sequences of state powers and matrix-commutator powers.
Their nonzero index types are proved finite, so zero-coupling termination and
stationary cases require no special nondegeneracy hypothesis.
-/
namespace Krylov.FactorTwoTheorem
open Matrix
open scoped InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Linear transport carries membership in a genuine polynomial cyclic span
into the corresponding coordinate cyclic span. -/
theorem linear_map_mem_cyclic {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (L : E →ₗ[ℂ] F) (f : ℕ → E) {x : E}
    (hx : x ∈ Submodule.span ℂ (Set.range f)) :
    L x ∈ Submodule.span ℂ (Set.range (fun k => L (f k))) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact Submodule.subset_span ⟨k, rfl⟩
  | zero => simp
  | add y z hy hz ihy ihz => simpa only [map_add] using Submodule.add_mem _ ihy ihz
  | smul c y hy ihy => simpa only [map_smul] using Submodule.smul_mem _ c ihy

/-- Actual Hamiltonian evolution belongs to its actual state cyclic space. -/
theorem state_evolution_mem_cyclic (G : Matrix ι ι ℂ) (ψ : ι → ℂ) (t : ℝ) :
    UnitaryEvolution.evolvedVector G ψ t ∈
      FactorTwoFinite.cyclicSpan (FactorTwoFinite.stateSequence G ψ) := by
  have h := CyclicEvolution.exp_mulVec_mem_cyclic G ψ (-((t : ℂ) * Complex.I))
  exact linear_map_mem_cyclic (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap
    (fun k => G ^ k *ᵥ ψ) h

/-- Rank-one evolution is the actual conjugation of its initial density. -/
theorem pure_conjugation (U : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    FactorTwo.pureSeed (U *ᵥ ψ) = U * FactorTwo.pureSeed ψ * Uᴴ := by
  unfold FactorTwo.pureSeed
  rw [FactorTwo.mul_outer, FactorTwo.outer_mul, Matrix.conjTranspose_conjTranspose]

/-- The actual evolved rank-one density belongs to the actual commutator
cyclic space; this is supplied by the matrix-exponential series, not assumed. -/
theorem pure_evolution_mem_cyclic (G : Matrix ι ι ℂ) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (t : ℝ) :
    FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector G ψ t)
      (UnitaryEvolution.evolvedVector G ψ t) ∈
      FactorTwoFinite.cyclicSpan (FactorTwoFinite.operatorSequence G ψ) := by
  have h := CyclicEvolution.unitary_evolution_mem_cyclic G (FactorTwo.pureSeed ψ) hG t
  have h' : UnitaryEvolution.propagator G t * FactorTwo.pureSeed ψ *
      (UnitaryEvolution.propagator G t)ᴴ ∈
      Submodule.span ℂ (Set.range (fun k : ℕ =>
        (FactorTwo.commutator G ^ k) (FactorTwo.pureSeed ψ))) := by
    simpa only [UnitaryEvolution.propagator, Complex.ofReal_neg, neg_mul] using h
  rw [← pure_conjugation] at h'
  exact linear_map_mem_cyclic FactorTwo.rowVectorize.toLinearMap
    (fun k => (FactorTwo.commutator G ^ k) (FactorTwo.pureSeed ψ)) h'

/-- The universal finite-dimensional factor-two theorem for every actual
unit seed, Hermitian Hamiltonian, and real time. Both complexities are defined
by the genuine normalized Gram-Schmidt Krylov constructions. -/
theorem finite_dimensional_factor_two (G : Matrix ι ι ℂ) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (hψ : ‖UnitaryEvolution.hilbertVector ψ‖ = 1) (t : ℝ) :
    2 * FactorTwoFinite.complexity (FactorTwoFinite.stateSequence G ψ)
        (UnitaryEvolution.evolvedVector G ψ t) ≤
      FactorTwoFinite.complexity (FactorTwoFinite.operatorSequence G ψ)
        (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector G ψ t)
          (UnitaryEvolution.evolvedVector G ψ t)) := by
  exact FactorTwoFinite.factor_two G hG ψ _
    (UnitaryEvolution.evolvedVector_unit G hG ψ hψ t)
    (state_evolution_mem_cyclic G ψ t) (pure_evolution_mem_cyclic G hG ψ t)

end
end Krylov.FactorTwoTheorem
