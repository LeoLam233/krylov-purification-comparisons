import Krylov.MatrixGSBridge

namespace Krylov.GSUnitaryTransport
open Matrix OperatorBridge UnitaryCovariance FactorTwoFinite
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000

theorem complexity_isometry {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : E ≃ₗᵢ[ℂ] F) (f : ℕ → E) (x : E) :
    complexity (fun n => T (f n)) (T x) = complexity f x := by
  classical
  have he (n : ℕ) := PhysicalSpectralPolynomials.isometry_gramSchmidtNormed T f n
  let e : GSIndex f ≃ GSIndex (fun n => T (f n)) :=
    { toFun := fun k => ⟨k.val, by
        change gramSchmidtNormed ℂ (fun n => T (f n)) k.val ≠ 0
        rw [← he]
        exact fun hz => k.property (T.injective (by simpa using hz))⟩
      invFun := fun k => ⟨k.val, by
        change gramSchmidtNormed ℂ f k.val ≠ 0
        intro hz
        apply k.property
        rw [← he,hz,map_zero]⟩
      left_inv := fun k => by apply Subtype.ext; rfl
      right_inv := fun k => by apply Subtype.ext; rfl }
  symm
  unfold complexity probability
  apply Fintype.sum_equiv e
  intro k
  change (k.val : ℝ)*‖⟪gramSchmidtNormed ℂ f k.val,x⟫_ℂ‖^2 =
    (k.val : ℝ)*‖⟪gramSchmidtNormed ℂ (fun n => T (f n)) k.val,T x⟫_ℂ‖^2
  rw [← he,T.inner_map_map]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixChange (Q : Operator ι) (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1) :
    Operator ι ≃ₗ[ℂ] Operator ι where
  toFun := changeBasis Q
  invFun := changeBasis Qᴴ
  left_inv A := by
    simpa using changeBasis_inverse Qᴴ A (by simpa using hQ')
  right_inv A := changeBasis_inverse Q A hQ
  map_add' A B := by simp [changeBasis,mul_add,add_mul]
  map_smul' c A := changeBasis_smul Q A c

def rowChange (Q : Operator ι) (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1) :
    EuclideanSpace ℂ (ι×ι) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ι×ι) :=
  ((FactorTwo.rowVectorize (ι := ι)).symm.trans
    ((matrixChange Q hQ hQ').trans FactorTwo.rowVectorize)).isometryOfInner (by
      intro x y
      obtain ⟨A,rfl⟩ := FactorTwo.rowVectorize.surjective x
      obtain ⟨B,rfl⟩ := FactorTwo.rowVectorize.surjective y
      simp only [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,
        FactorTwo.rowVectorize_inner]
      exact hsInner_changeBasis Q A B hQ')

lemma rowChange_apply (Q : Operator ι) (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1)
    (A : Operator ι) : rowChange Q hQ hQ' (FactorTwo.rowVectorize A) =
      FactorTwo.rowVectorize (changeBasis Q A) := by
  simp [rowChange,matrixChange]

lemma normalized_change (Q : Operator ι) (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1)
    (A : Operator ι) :
    rowChange Q hQ hQ' (PhysicalCurvatureNecessary.normalizedSeed A) =
      PhysicalCurvatureNecessary.normalizedSeed (changeBasis Q A) := by
  have hn := (rowChange Q hQ hQ').norm_map (FactorTwo.rowVectorize A)
  rw [rowChange_apply] at hn
  simp only [PhysicalCurvatureNecessary.normalizedSeed,map_smul,rowChange_apply,hn]

lemma commutator_power_change (Q H A : Operator ι) (hQ' : Q*Qᴴ=1) (n : ℕ) :
    changeBasis Q ((FactorTwo.commutator H^n) A) =
      (FactorTwo.commutator (changeBasis Q H)^n) (changeBasis Q A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,
      FactorTwo.commutator_apply,changeBasis_commutator Q H _ hQ',ih]
    rfl

theorem normalized_power_change (Q H A : Operator ι) (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1)
    (n : ℕ) :
    PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian (changeBasis Q H))
      (PhysicalCurvatureNecessary.normalizedSeed (changeBasis Q A)) n =
    rowChange Q hQ hQ' (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H)
      (PhysicalCurvatureNecessary.normalizedSeed A) n) := by
  have hn := (rowChange Q hQ hQ').norm_map (FactorTwo.rowVectorize A)
  rw [rowChange_apply] at hn
  simp only [PerturbedDynamics.powerSequence,PhysicalCurvatureNecessary.normalizedSeed,
    map_smul,PerturbedDynamics.liouvillian_power_rowVectorize,rowChange_apply,
    commutator_power_change Q H A hQ',hn]

theorem polynomial_change (Q H A : Operator ι) (hQ' : Q*Qᴴ=1)
    (p : Polynomial ℂ) :
    changeBasis Q ((Polynomial.aeval (FactorTwo.commutator H)) p A) =
      (Polynomial.aeval (FactorTwo.commutator (changeBasis Q H))) p (changeBasis Q A) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add,LinearMap.add_apply,changeBasis,mul_add,add_mul] using congrArg₂ (·+·) hp hq
  | monomial n c =>
    simp [Polynomial.aeval_monomial,Module.End.mul_apply,changeBasis_smul,
      commutator_power_change Q H A hQ']

theorem normalized_evolution_change (Q H A : Operator ι) (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1)
    (hH : H.IsHermitian) (t : ℝ) :
    TaylorRemainder.evolution
      (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian (changeBasis Q H)))
      (PhysicalCurvatureNecessary.normalizedSeed (changeBasis Q A)) t =
    rowChange Q hQ hQ' (TaylorRemainder.evolution
      (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian H))
      (PhysicalCurvatureNecessary.normalizedSeed A) t) := by
  have hH' : (changeBasis Q H).IsHermitian := by
    rw [Matrix.IsHermitian,changeBasis_conjTranspose,hH.eq]
  rw [MatrixGSBridge.evolution_normalized _ _ hH',MatrixGSBridge.evolution_normalized _ _ hH]
  have hn := (rowChange Q hQ hQ').norm_map (FactorTwo.rowVectorize A)
  rw [rowChange_apply] at hn
  simp only [map_smul,rowChange_apply,hn,evolution_changeBasis Q H A t hQ hQ']

theorem probability_changeBasis (Q H A : Operator ι) (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1)
    (hH : H.IsHermitian) (n : ℕ) (t : ℝ) :
    ‖⟪gramSchmidtNormed ℂ
        (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian (changeBasis Q H))
          (PhysicalCurvatureNecessary.normalizedSeed (changeBasis Q A))) n,
      TaylorRemainder.evolution
        (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian (changeBasis Q H)))
        (PhysicalCurvatureNecessary.normalizedSeed (changeBasis Q A)) t⟫_ℂ‖^2 =
    ‖⟪gramSchmidtNormed ℂ
        (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H)
          (PhysicalCurvatureNecessary.normalizedSeed A)) n,
      TaylorRemainder.evolution (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian H))
        (PhysicalCurvatureNecessary.normalizedSeed A) t⟫_ℂ‖^2 := by
  have hf := funext (normalized_power_change Q H A hQ hQ')
  rw [hf,normalized_evolution_change Q H A hQ hQ' hH t,
    ← PhysicalSpectralPolynomials.isometry_gramSchmidtNormed,
    (rowChange Q hQ hQ').inner_map_map]

theorem actual_changeBasis (Q H A : Operator ι) (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1)
    (hH : H.IsHermitian) (t : ℝ) :
    PerturbedDynamics.actualComplexity
      (PerturbedDynamics.liouvillian (changeBasis Q H))
      (PhysicalCurvatureNecessary.normalizedSeed (changeBasis Q A)) t =
    PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian H)
      (PhysicalCurvatureNecessary.normalizedSeed A) t := by
  let T := rowChange Q hQ hQ'
  have hH' : (changeBasis Q H).IsHermitian := by
    rw [Matrix.IsHermitian,changeBasis_conjTranspose,hH.eq]
  have hp (n : ℕ) :
      PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian (changeBasis Q H))
        (PhysicalCurvatureNecessary.normalizedSeed (changeBasis Q A)) n =
      T (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H)
        (PhysicalCurvatureNecessary.normalizedSeed A) n) := by
    have hn := T.norm_map (FactorTwo.rowVectorize A)
    rw [rowChange_apply] at hn
    simp only [PerturbedDynamics.powerSequence,PhysicalCurvatureNecessary.normalizedSeed,
      map_smul,PerturbedDynamics.liouvillian_power_rowVectorize,T,rowChange_apply,
      commutator_power_change Q H A hQ',hn]
  have hx : TaylorRemainder.evolution
      (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian (changeBasis Q H)))
      (PhysicalCurvatureNecessary.normalizedSeed (changeBasis Q A)) t =
      T (TaylorRemainder.evolution
        (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian H))
        (PhysicalCurvatureNecessary.normalizedSeed A) t) := by
    rw [MatrixGSBridge.evolution_normalized _ _ hH',MatrixGSBridge.evolution_normalized _ _ hH]
    have hn := T.norm_map (FactorTwo.rowVectorize A)
    rw [rowChange_apply] at hn
    simp only [T,map_smul,rowChange_apply,hn,evolution_changeBasis Q H A t hQ hQ']
  unfold PerturbedDynamics.actualComplexity
  rw [show PerturbedDynamics.powerSequence
      (PerturbedDynamics.liouvillian (changeBasis Q H))
      (PhysicalCurvatureNecessary.normalizedSeed (changeBasis Q A)) =
      (fun n => T (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H)
        (PhysicalCurvatureNecessary.normalizedSeed A) n)) from funext hp]
  rw [hx,complexity_isometry]

end
end Krylov.GSUnitaryTransport
