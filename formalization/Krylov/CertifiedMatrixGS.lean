import Krylov.CertifiedGS
import Krylov.MatrixGSBridge

namespace Krylov.CertifiedMatrixGS
open Matrix OperatorBridge PhysicalCurvatureNecessary MatrixGSBridge
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One reusable source-API bridge for all finite certified polynomial
operator chains. Zero padding and arbitrary nonzero leading phases are allowed. -/
theorem actual_eq_matrix_sum {d : ℕ} (H A : Operator ι)
    (hH : H.IsHermitian) (hA : A ≠ 0)
    (v : Fin d → Operator ι) (p : Fin d → Polynomial ℂ)
    (hp : ∀ i, v i = (Polynomial.aeval (FactorTwo.commutator H)) (p i) A)
    (hd : ∀ i, (p i).degree = (i.val : WithBot ℕ))
    (ho : Pairwise (fun i j => hsInner (v i) (v j)=0))
    (hc : Submodule.span ℂ (Set.range v) =
      ConcreteChains.cyclicSpan (FactorTwo.commutator H) A) (t : ℝ) :
    PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian H)
      (normalizedSeed A) t =
      ∑ i : Fin d, (i.val : ℝ)*UnitaryCovariance.matrixProbability H A (v i) t := by
  let c : ℂ := (‖FactorTwo.rowVectorize A‖⁻¹ : ℝ)
  have hn : ‖FactorTwo.rowVectorize A‖ ≠ 0 := by
    intro hz
    apply hA
    exact FactorTwo.rowVectorize.injective (by simpa using norm_eq_zero.mp hz)
  have hcn : c ≠ 0 := by
    change (↑(‖FactorTwo.rowVectorize A‖⁻¹) : ℂ) ≠ 0
    exact_mod_cast inv_ne_zero hn
  have hv (i : Fin d) : polynomialMap H A (p i) = c • FactorTwo.rowVectorize (v i) := by
    rw [hp i]
    rfl
  have hg : Pairwise (fun i j =>
      ⟪polynomialMap H A (p i),polynomialMap H A (p j)⟫_ℂ=0) := by
    intro i j hij
    rw [hv,hv,inner_smul_left,inner_smul_right,FactorTwo.rowVectorize_inner]
    change star c * (c * hsInner (v i) (v j)) = 0
    rw [ho hij]
    simp
  have hcomplete (k : ℕ) : polynomialMap H A (Polynomial.X^k) ∈
      Submodule.span ℂ (Set.range (fun i => polynomialMap H A (p i))) := by
    have hm : ((FactorTwo.commutator H)^k) A ∈ Submodule.span ℂ (Set.range v) := by
      rw [hc]
      exact Submodule.subset_span ⟨k,rfl⟩
    have ht : ∀ y ∈ Submodule.span ℂ (Set.range v),
        c • FactorTwo.rowVectorize y ∈
          Submodule.span ℂ (Set.range (fun i => polynomialMap H A (p i))) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i,rfl⟩ := hy
        rw [← hv i]
        exact Submodule.subset_span ⟨i,rfl⟩
      | zero => simp
      | add y z hy hz ihy ihz =>
        simpa [map_add,smul_add] using Submodule.add_mem _ ihy ihz
      | smul a y hy ih =>
        simpa [map_smul,smul_smul,mul_comm] using Submodule.smul_mem _ a ih
    simpa [polynomialMap,c] using ht _ hm
  have h := CertifiedGS.complexity_eq_of_polynomials (polynomialMap H A) p hd hg
    hcomplete (TaylorRemainder.evolution
      (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian H))
      (normalizedSeed A) t)
  simp_rw [polynomialMap_power] at h
  rw [PerturbedDynamics.actualComplexity,h]
  apply Finset.sum_congr rfl
  intro i _
  rw [hv,scaled_probability H A (v i) hH t c hcn]

end
end Krylov.CertifiedMatrixGS
