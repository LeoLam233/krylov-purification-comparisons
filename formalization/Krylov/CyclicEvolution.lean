import Krylov.FactorTwo
import Krylov.ConcreteChains

/-! Matrix exponentials preserve actual finite-dimensional cyclic subspaces.
The proof uses the convergent exponential series and closedness of finite-
dimensional submodules; no polynomial approximation is postulated. -/
namespace Krylov.CyclicEvolution
open Matrix
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vectorEvaluation (ψ : ι → ℂ) : Matrix ι ι ℂ →ₗ[ℂ] (ι → ℂ) where
  toFun A := A *ᵥ ψ
  map_add' A B := Matrix.add_mulVec A B ψ
  map_smul' c A := by ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

def stateCyclicSpan (G : Matrix ι ι ℂ) (ψ : ι → ℂ) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ (Set.range (fun k : ℕ => G^k *ᵥ ψ))

theorem exp_mulVec_mem_cyclic (G : Matrix ι ι ℂ) (ψ : ι → ℂ) (c : ℂ) :
    NormedSpace.exp ℂ (c • G) *ᵥ ψ ∈ stateCyclicSpan G ψ := by
  letI : SeminormedRing (Matrix ι ι ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  let S := stateCyclicSpan G ψ
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • G)).map
    (vectorEvaluation ψ) (vectorEvaluation ψ).continuous_of_finiteDimensional
  apply S.closed_of_finiteDimensional.mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply S.sum_mem
  intro k _
  change (vectorEvaluation ψ) (((k.factorial : ℂ)⁻¹) • (c • G)^k) ∈ S
  rw [smul_pow, smul_smul, map_smul]
  apply S.smul_mem
  exact Submodule.subset_span ⟨k,rfl⟩


section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

def left (a : A) : A →L[ℂ] A := (ContinuousLinearMap.mul ℂ A) a
def right (a : A) : A →L[ℂ] A := (ContinuousLinearMap.mul ℂ A).flip a

@[simp] theorem left_apply (a x : A) : left a x = a*x := rfl
@[simp] theorem right_apply (a x : A) : right a x = x*a := rfl

theorem left_pow_apply (a x : A) (n : ℕ) : (left a ^ n) x = a^n*x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ',ContinuousLinearMap.mul_apply,left_apply,ih,pow_succ']; simp [mul_assoc]

theorem right_pow_apply (a x : A) (n : ℕ) : (right a ^ n) x = x*a^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ',ContinuousLinearMap.mul_apply,right_apply,ih,pow_succ]; simp [mul_assoc]

theorem exp_left_apply (a x : A) : NormedSpace.exp ℂ (left a) x = NormedSpace.exp ℂ a * x := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (left a)).map
    ((ContinuousLinearMap.apply ℂ A) x) ((ContinuousLinearMap.apply ℂ A) x).continuous
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) a).map (right x) (right x).continuous
  have hh1 : HasSum (fun n => ((n.factorial : ℂ)⁻¹) • (a^n*x))
      (NormedSpace.exp ℂ (left a) x) := by
    simpa [Function.comp_def,left_pow_apply] using h1
  have hh2 : HasSum (fun n => ((n.factorial : ℂ)⁻¹) • (a^n*x))
      (NormedSpace.exp ℂ a*x) := by
    simpa [Function.comp_def,smul_mul_assoc] using h2
  exact hh1.unique hh2

theorem exp_right_apply (a x : A) : NormedSpace.exp ℂ (right a) x = x * NormedSpace.exp ℂ a := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (right a)).map
    ((ContinuousLinearMap.apply ℂ A) x) ((ContinuousLinearMap.apply ℂ A) x).continuous
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) a).map (left x) (left x).continuous
  have hh1 : HasSum (fun n => ((n.factorial : ℂ)⁻¹) • (x*a^n))
      (NormedSpace.exp ℂ (right a) x) := by
    simpa [Function.comp_def,right_pow_apply] using h1
  have hh2 : HasSum (fun n => ((n.factorial : ℂ)⁻¹) • (x*a^n))
      (x*NormedSpace.exp ℂ a) := by
    simpa [Function.comp_def,mul_smul_comm] using h2
  exact hh1.unique hh2

def ad (a : A) : A →L[ℂ] A := left a-right a

@[simp] theorem ad_apply (a x : A) : ad a x = a*x-x*a := rfl

theorem exp_ad_apply (a x : A) (c : ℂ) :
    NormedSpace.exp ℂ (c • ad a) x =
      NormedSpace.exp ℂ (c • a) * x * NormedSpace.exp ℂ ((-c) • a) := by
  have he : c • ad a = left (c • a) + right ((-c) • a) := by
    ext y
    simp [ad,smul_sub,smul_mul_assoc,mul_smul_comm,sub_eq_add_neg]
  have hc : Commute (left (c • a)) (right ((-c) • a)) := by
    ext y
    simp [ContinuousLinearMap.mul_apply,mul_assoc]
  rw [he, NormedSpace.exp_add_of_commute hc, ContinuousLinearMap.mul_apply,
    exp_left_apply, exp_right_apply]
  simp [mul_assoc]

end Algebra


section Endomorphism
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

theorem exp_end_apply_mem_cyclic (L : E →L[ℂ] E) (v : E) (c : ℂ) :
    NormedSpace.exp ℂ (c • L) v ∈
      Submodule.span ℂ (Set.range (fun k : ℕ => (L^k) v)) := by
  let S := Submodule.span ℂ (Set.range (fun k : ℕ => (L^k) v))
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • L)).map
    ((ContinuousLinearMap.apply ℂ E) v) ((ContinuousLinearMap.apply ℂ E) v).continuous
  apply S.closed_of_finiteDimensional.mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply S.sum_mem
  intro k _
  change (((k.factorial : ℂ)⁻¹) • (c • L)^k) v ∈ S
  rw [smul_pow, smul_smul, ContinuousLinearMap.smul_apply]
  apply S.smul_mem
  exact Submodule.subset_span ⟨k,rfl⟩
end Endomorphism

section Matrices
attribute [local instance] Matrix.linftyOpSemiNormedRing Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

theorem ad_pow_eq_commutator (G A : Matrix ι ι ℂ) (k : ℕ) :
    (ad G ^ k) A = (FactorTwo.commutator G ^ k) A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',ContinuousLinearMap.mul_apply,pow_succ',Module.End.mul_apply,
      ad_apply,ih,FactorTwo.commutator_apply]

theorem exponential_conjugation_mem_cyclic (G A : Matrix ι ι ℂ) (c : ℂ) :
    NormedSpace.exp ℂ (c • G) * A * NormedSpace.exp ℂ ((-c) • G) ∈
      Submodule.span ℂ (Set.range (fun k : ℕ => (FactorTwo.commutator G ^ k) A)) := by
  have h := exp_end_apply_mem_cyclic (ad G) A c
  rw [exp_ad_apply] at h
  simpa only [ad_pow_eq_commutator] using h

theorem unitary_evolution_mem_cyclic (G A : Matrix ι ι ℂ)
    (hG : G.IsHermitian) (t : ℝ) :
    let U := NormedSpace.exp ℂ ((((-t : ℝ) : ℂ)*Complex.I) • G)
    U * A * Uᴴ ∈
      Submodule.span ℂ (Set.range (fun k : ℕ => (FactorTwo.commutator G ^ k) A)) := by
  dsimp only
  rw [← Matrix.exp_conjTranspose]
  have he : (((((-t : ℝ) : ℂ)*Complex.I) • G))ᴴ =
      (-(((-t : ℝ) : ℂ)*Complex.I)) • G := by
    simp [Matrix.conjTranspose_smul,hG.eq,Complex.star_def]
  rw [he]
  exact exponential_conjugation_mem_cyclic G A _
end Matrices

end
end Krylov.CyclicEvolution
