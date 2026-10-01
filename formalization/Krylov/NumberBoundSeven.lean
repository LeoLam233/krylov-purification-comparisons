import Krylov.PerturbedDynamics
import Krylov.Annihilator

namespace Krylov.NumberBoundSeven
open PerturbedDynamics FactorTwoFinite
open scoped InnerProductSpace
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A certified degree-seven annihilator supplies the original six-degree
number-operator bound; neither chain length nor termination is assumed. -/
theorem number_bound_of_annihilator (L : E →L[ℂ] E) (v : E) (a b c : ℂ)
    (h7 : (L^7) v = a • (L^5) v + b • (L^3) v + c • L v) :
    ‖numberOperator (powerSequence L v)‖ ≤ 6 := by
  have hzero : gramSchmidtNormed ℂ (KrylovTermination.sequence L v) 7 = 0 := by
    apply (KrylovTermination.normed_zero_iff _ _).2
    apply (KrylovTermination.gram_zero_iff_mem _ _).2
    change (L^7) v ∈ Submodule.span ℂ (KrylovTermination.sequence L v '' Set.Iio 7)
    rw [h7]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨5,by norm_num,rfl⟩
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨3,by norm_num,rfl⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨1,by norm_num,by simp [KrylovTermination.sequence]⟩
  apply norm_numberOperator_le _ (by norm_num)
  intro k
  have hk : k.val ≤ 6 := by
    by_contra hn
    have hz := KrylovTermination.zero_forces_later_zero L v hzero (show 7≤k.val by omega)
    exact k.property hz
  exact_mod_cast hk

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_number_bound (G : Matrix ι ι ℂ) (a b c : ℂ)
    (hcert : ∀ X : Matrix ι ι ℂ,
      (FactorTwo.commutator G^7) X = a • (FactorTwo.commutator G^5) X +
        b • (FactorTwo.commutator G^3) X + c • FactorTwo.commutator G X)
    (v : EuclideanSpace ℂ (ι×ι)) :
    ‖numberOperator (powerSequence (liouvillian G) v)‖ ≤ 6 := by
  apply number_bound_of_annihilator (liouvillian G) v a b c
  let X := FactorTwo.rowVectorize.symm v
  have h := congrArg FactorTwo.rowVectorize (hcert X)
  simp only [map_add,map_smul] at h
  have hp (k : ℕ) : FactorTwo.rowVectorize ((FactorTwo.commutator G^k) X) =
      (liouvillian G^k) v := by
    rw [← liouvillian_power_rowVectorize]
    simp [X]
  rw [hp 7,hp 5,hp 3] at h
  have h1 := hp 1
  simp only [pow_one] at h1
  rw [h1] at h
  exact h
end Matrix

theorem mixed_number_six (δ : ℝ) :
    ‖numberOperator (powerSequence (liouvillian (complexHamiltonian δ)) mixedVector)‖ ≤ 6 := by
  let a : ℂ := 6*(1+5*(δ : ℂ)^2)
  let b : ℂ := -(9*(1+5*(δ : ℂ)^2)^2)
  let c : ℂ := 4*(1+5*(δ : ℂ)^2)^3-432*(δ : ℂ)^4
  apply matrix_number_bound (complexHamiltonian δ) a b c _ mixedVector
  intro X
  have h := Annihilator.degree_seven (δ : ℂ) X
  simp only [Annihilator.L,Annihilator.H_real] at h
  change (FactorTwo.commutator (complexHamiltonian δ)^7) X -
    (6*(1+5*(δ:ℂ)^2)) • (FactorTwo.commutator (complexHamiltonian δ)^5) X +
    (9*(1+5*(δ:ℂ)^2)^2) • (FactorTwo.commutator (complexHamiltonian δ)^3) X +
    (-4*(1+5*(δ:ℂ)^2)^3+432*(δ:ℂ)^4) • FactorTwo.commutator (complexHamiltonian δ) X = 0 at h
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.zero_apply,smul_eq_mul] at hij ⊢
  simp only [a,b,c,FactorTwo.commutator_apply,Matrix.sub_apply] at hij ⊢
  linear_combination hij

theorem purified_number_six (δ : ℝ) :
    ‖numberOperator (powerSequence (liouvillian (purifiedGenerator δ)) purifiedVector)‖ ≤ 6 := by
  let a : ℂ := 6*(1+5*(δ : ℂ)^2)
  let b : ℂ := -(9*(1+5*(δ : ℂ)^2)^2)
  let c : ℂ := 4*(1+5*(δ : ℂ)^2)^3-432*(δ : ℂ)^4
  apply matrix_number_bound (purifiedGenerator δ) a b c _ purifiedVector
  intro X
  have h := Annihilator.lifted_degree_seven (δ : ℂ) X
  simp only [Annihilator.liftedL,Annihilator.H_real] at h
  change (FactorTwo.commutator (purifiedGenerator δ)^7) X -
    (6*(1+5*(δ:ℂ)^2)) • (FactorTwo.commutator (purifiedGenerator δ)^5) X +
    (9*(1+5*(δ:ℂ)^2)^2) • (FactorTwo.commutator (purifiedGenerator δ)^3) X +
    (-4*(1+5*(δ:ℂ)^2)^3+432*(δ:ℂ)^4) • FactorTwo.commutator (purifiedGenerator δ) X = 0 at h
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.zero_apply,smul_eq_mul] at hij ⊢
  simp only [a,b,c,FactorTwo.commutator_apply,Matrix.sub_apply] at hij ⊢
  linear_combination hij

end
end Krylov.NumberBoundSeven
