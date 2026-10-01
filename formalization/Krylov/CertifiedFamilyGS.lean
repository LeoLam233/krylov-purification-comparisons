import Krylov.CertifiedMatrixGS
import Krylov.CertifiedPolynomialDegrees

/-! Uniform identification of the three- and five-atom spectral families
with normalized Gram--Schmidt complexity of the actual matrix generator. -/
namespace Krylov.CertifiedFamilyGS
open Matrix OperatorBridge ConcreteChains MatrixGSBridge
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Diagonal form of the generic certified matrix-chain theorem. -/
theorem actual_eq_chainComplexity {d : ℕ} (E : ι → ℝ) (A : Operator ι)
    (hA : A ≠ 0) (v : Fin d → Operator ι) (p : Fin d → Polynomial ℂ)
    (hp : ∀ i, v i=(Polynomial.aeval (OperatorBridge.liouvillian E)) (p i) A)
    (hd : ∀ i, (p i).degree=(i.val : WithBot ℕ))
    (ho : Pairwise (fun i j => hsInner (v i) (v j)=0))
    (hc : Submodule.span ℂ (Set.range v)=ConcreteChains.cyclicSpan (OperatorBridge.liouvillian E) A)
    (t : ℝ) :
    PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian (hamiltonian E))
      (PhysicalCurvatureNecessary.normalizedSeed A) t = chainComplexity E A v t := by
  rw [CertifiedMatrixGS.actual_eq_matrix_sum (hamiltonian E) A (diagonal_hermitian E) hA v p]
  · simp only [chainComplexity,UnitaryCovariance.diagonal_probability]
  · simpa only [diagonal_commutator] using hp
  · exact hd
  · exact ho
  · simpa only [diagonal_commutator] using hc

/-- Every nondegenerate three-atom operator certificate computes the actual
normalized GS complexity, with no assumption on unused ambient directions. -/
theorem three_atom {E : ι → ℝ} {A : Operator ι} {μ s : ℝ}
    (h : ThreeAtomOperator.Data E A μ s) (t : ℝ) :
    PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian (hamiltonian E))
      (PhysicalCurvatureNecessary.normalizedSeed A) t =
        chainComplexity E A (ThreeAtomOperator.chain E A μ) t := by
  have hA : A ≠ 0 := by
    intro hz
    have hh := ThreeAtomOperator.seed_norm h
    simp [hz,hsInner] at hh
    exact h.scale_pos.ne' (Complex.ofReal_eq_zero.mp hh.symm)
  apply actual_eq_chainComplexity E A hA _ (ThreeAtomOperator.polynomial μ)
  · intro i; rfl
  · exact CertifiedPolynomialDegrees.three μ
  · intro i j hij
    simp [ThreeAtomOperator.gram h,hij]
  · exact ThreeAtomOperator.chain_spans_cyclic h

/-- The closed three-atom formula is an equality in the literal GS API. -/
theorem three_atom_formula {E : ι → ℝ} {A : Operator ι} {μ s : ℝ}
    (h : ThreeAtomOperator.Data E A μ s) (t : ℝ) :
    PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian (hamiltonian E))
      (PhysicalCurvatureNecessary.normalizedSeed A) t = Qubit.threeAtom μ t := by
  rw [three_atom h,ThreeAtomOperator.complexity_eq_threeAtom h]

/-- All admissible five-atom masses use the same actual GS API. The two
nonmonic leading coefficients are certified nonzero from the mass hypotheses. -/
theorem five_atom {E : ι → ℝ} {A : Operator ι} {u v s : ℝ}
    (h : FiveAtom.Data E A u v s) (t : ℝ) :
    PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian (hamiltonian E))
      (PhysicalCurvatureNecessary.normalizedSeed A) t =
        chainComplexity E A (FiveAtom.chain E A u v) t := by
  have hA : A ≠ 0 := by
    intro hz
    have hh := FiveAtom.seed_norm h
    simp [hz,hsInner] at hh
    exact h.scale_pos.ne' (Complex.ofReal_eq_zero.mp hh.symm)
  apply actual_eq_chainComplexity E A hA _ (FiveAtom.polynomial u v)
  · intro i; rfl
  · exact CertifiedPolynomialDegrees.five u v (FiveAtom.m2_pos h).ne' (FiveAtom.n2_pos h).ne'
  · intro i j hij
    simp [FiveAtom.gram h,hij]
  · exact FiveAtom.chain_spans_cyclic h

end
end Krylov.CertifiedFamilyGS
