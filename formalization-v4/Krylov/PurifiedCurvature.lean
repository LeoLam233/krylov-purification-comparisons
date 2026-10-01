import Krylov.Perturbation
import Krylov.PurifiedCovariance
import Krylov.FactorTwo

/-! Exact actual rank-one seed and commutator curvature for H_delta ⊗ I. -/
namespace Krylov.PurifiedCurvature
open Matrix OperatorBridge
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
abbrev Index := Fin 3 × Fin 3

def coeff : Fin 3 → ℝ := ![4,1,3]
def pureVector (a : Index) : ℂ :=
  if a.1=a.2 then (coeff a.1 : ℂ)*(States.sR : ℂ) else 0

def generator (δ : ℝ) : Matrix Index Index ℂ :=
  PurifiedCovariance.lift ((Perturbation.hamiltonian δ).map Complex.ofReal)

theorem pureVector_root (a : Index) : pureVector a = (States.rootR a.1 a.2 : ℂ) := by
  rcases a with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [pureVector,coeff,States.rootR,Matrix.diagonal]

theorem seed_eq : FactorTwo.pureSeed pureVector = PurifiedCovariance.originalSeed := by
  ext a b
  simp [FactorTwo.pureSeed,FactorTwo.outer,PurifiedCovariance.originalSeed,
    Purification.pureSeed,PurifiedCovariance.originalRoot,pureVector_root]

theorem generator_hermitian (δ : ℝ) : (generator δ).IsHermitian := by
  change (generator δ)ᴴ=generator δ
  rw [generator,PurifiedCovariance.lift_adjoint]
  apply congrArg PurifiedCovariance.lift
  have hh := Perturbation.hermitian δ
  simpa [UnitaryCovariance.complexify_transpose] using
    congrArg (fun B => B.map Complex.ofReal) hh


theorem applied_entry (δ : ℝ) (a : Index) :
    (generator δ *ᵥ pureVector) a =
      (Perturbation.hamiltonian δ a.1 a.2 : ℂ) * (coeff a.2 : ℂ) * (States.sR : ℂ) := by
  rcases a with ⟨i,j⟩
  simp [generator,PurifiedCovariance.lift,Matrix.kronecker_apply,
    Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.one_apply,pureVector,
    ite_mul,mul_ite,mul_assoc]

theorem vector_norm : FactorTwo.vectorInner pureVector pureVector = 1 := by
  norm_num [FactorTwo.vectorInner,pureVector,coeff,Fintype.sum_prod_type,
    Fin.sum_univ_three,Complex.star_def,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  have h : ((States.sR : ℂ)^2) = 1/26 := by norm_num [←Complex.ofReal_pow,States.sR_sq]
  linear_combination 26*h

theorem first_moment (δ : ℝ) :
    FactorTwo.vectorInner pureVector (generator δ *ᵥ pureVector)=0 := by
  have h02 : (0:Fin 3) ≠ 2 := by decide
  have h12 : (1:Fin 3) ≠ 2 := by decide
  have h20 : (2:Fin 3) ≠ 0 := by decide
  have h21 : (2:Fin 3) ≠ 1 := by decide
  simp_rw [FactorTwo.vectorInner,applied_entry]
  norm_num [pureVector,coeff,Perturbation.hamiltonian,Fintype.sum_prod_type,
    Fin.sum_univ_three,Complex.star_def,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,h02,h12,h20,h21]

theorem second_moment (δ : ℝ) :
    FactorTwo.vectorInner (generator δ *ᵥ pureVector) (generator δ *ᵥ pureVector) =
      (((17+65*δ^2)/26 : ℝ) : ℂ) := by
  simp_rw [FactorTwo.vectorInner,applied_entry]
  norm_num [coeff,Perturbation.hamiltonian,Fintype.sum_prod_type,
    Fin.sum_univ_three,Complex.star_def,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  have h : ((States.sR : ℂ)^2) = 1/26 := by norm_num [←Complex.ofReal_pow,States.sR_sq]
  linear_combination (17+65*(δ:ℂ)^2)*h

theorem reverse_first_moment (δ : ℝ) :
    FactorTwo.vectorInner (generator δ *ᵥ pureVector) pureVector=0 := by
  have h := congrArg star (first_moment δ)
  simpa [FactorTwo.vectorInner,star_sum,StarMul.star_mul,mul_comm] using h

theorem commutator_outer (δ : ℝ) :
    FactorTwo.commutator (generator δ) (FactorTwo.pureSeed pureVector) =
      FactorTwo.outer (generator δ *ᵥ pureVector) pureVector -
      FactorTwo.outer pureVector (generator δ *ᵥ pureVector) := by
  rw [FactorTwo.commutator_apply,FactorTwo.pureSeed,FactorTwo.mul_outer,
    FactorTwo.outer_mul,(generator_hermitian δ).eq]

theorem hs_outer (u v x y : Index → ℂ) :
    hsInner (FactorTwo.outer u v) (FactorTwo.outer x y) =
      FactorTwo.vectorInner u x * star (FactorTwo.vectorInner v y) := by
  have h := FactorTwo.outer_inner u v x y
  rw [FactorTwo.rowVectorize_inner] at h
  exact h

theorem hs_sub_left (A B C : Operator Index) : hsInner (A-B) C=hsInner A C-hsInner B C := by
  simp [hsInner,star_sub,sub_mul,Finset.sum_sub_distrib]
theorem hs_sub_right (A B C : Operator Index) : hsInner A (B-C)=hsInner A B-hsInner A C := by
  simp [hsInner,mul_sub,Finset.sum_sub_distrib]

theorem seed_hs_norm : hsInner PurifiedCovariance.originalSeed PurifiedCovariance.originalSeed = 1 := by
  rw [← seed_eq]
  change hsInner (FactorTwo.outer pureVector pureVector) (FactorTwo.outer pureVector pureVector)=1
  rw [hs_outer,vector_norm]
  simp

theorem commutator_hs_norm (δ : ℝ) :
    hsInner (FactorTwo.commutator (generator δ) PurifiedCovariance.originalSeed)
      (FactorTwo.commutator (generator δ) PurifiedCovariance.originalSeed) =
      (((17+65*δ^2)/13 : ℝ) : ℂ) := by
  rw [← seed_eq,commutator_outer,hs_sub_left,hs_sub_right,hs_sub_right]
  rw [hs_outer,hs_outer,hs_outer,hs_outer,
    vector_norm,first_moment,reverse_first_moment,second_moment]
  simp
  ring

end
end Krylov.PurifiedCurvature
