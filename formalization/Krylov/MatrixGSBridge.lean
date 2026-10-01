import Krylov.PhysicalCurvatureNecessary
import Krylov.PhysicalSpectralPolynomials

/-! Representation and normalization identities connecting certified matrix
chains with the source's actual Gram–Schmidt definitions. -/
namespace Krylov.MatrixGSBridge
open Matrix OperatorBridge PhysicalCurvatureNecessary
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma row_norm_sq (A : Operator ι) :
    ‖FactorTwo.rowVectorize A‖^2 = (hsInner A A).re := by
  rw [@norm_sq_eq_re_inner ℂ, FactorTwo.rowVectorize_inner]
  rfl

lemma evolution_normalized (H A : Operator ι) (hH : H.IsHermitian) (t : ℝ) :
    TaylorRemainder.evolution (PerturbedDynamics.skewGenerator
      (PerturbedDynamics.liouvillian H)) (normalizedSeed A) t =
      ((‖FactorTwo.rowVectorize A‖⁻¹ : ℝ) : ℂ) •
        FactorTwo.rowVectorize (UnitaryCovariance.evolution H A t) := by
  unfold normalizedSeed TaylorRemainder.evolution
  rw [map_smul]
  exact congrArg (fun x => ((‖FactorTwo.rowVectorize A‖⁻¹ : ℝ) : ℂ) • x)
    (PerturbedDynamics.evolution_rowVectorize H A hH t)

/-- Includes zero padded chain vectors: both sides then vanish by total division. -/
lemma normalized_probability (H A v : Operator ι) (hH : H.IsHermitian) (t : ℝ) :
    ‖⟪normalizedSeed v, TaylorRemainder.evolution
      (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian H))
      (normalizedSeed A) t⟫_ℂ‖^2 = UnitaryCovariance.matrixProbability H A v t := by
  rw [evolution_normalized H A hH t]
  simp only [normalizedSeed, inner_smul_left, inner_smul_right, norm_mul,
    Complex.norm_conj, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _), mul_pow, inv_pow,
    FactorTwo.rowVectorize_inner]
  rw [row_norm_sq A, row_norm_sq v]
  simp only [UnitaryCovariance.matrixProbability, Complex.normSq_eq_norm_sq, hsInner]
  ring

lemma diagonal_hermitian (E : ι → ℝ) : (hamiltonian E).IsHermitian := by
  ext i j
  by_cases h : i = j <;> simp [hamiltonian, Matrix.conjTranspose_apply, h, eq_comm]

lemma raw_probability (H A v : Operator ι) (hH : H.IsHermitian) (t : ℝ) :
    ‖⟪FactorTwo.rowVectorize v, TaylorRemainder.evolution
      (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian H))
      (normalizedSeed A) t⟫_ℂ‖^2 / ‖FactorTwo.rowVectorize v‖^2 =
      UnitaryCovariance.matrixProbability H A v t := by
  rw [evolution_normalized H A hH t]
  simp only [inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (norm_nonneg _), mul_pow, inv_pow,
    FactorTwo.rowVectorize_inner, row_norm_sq A, row_norm_sq v,
    UnitaryCovariance.matrixProbability, Complex.normSq_eq_norm_sq, hsInner]
  ring

/-- Uniform nonzero rescaling of a certified vector does not change its
normalized projection probability, including a zero padded vector. -/
lemma scaled_probability (H A v : Operator ι) (hH : H.IsHermitian) (t : ℝ)
    (c : ℂ) (hc : c ≠ 0) :
    ‖⟪c • FactorTwo.rowVectorize v, TaylorRemainder.evolution
      (PerturbedDynamics.skewGenerator (PerturbedDynamics.liouvillian H))
      (normalizedSeed A) t⟫_ℂ‖^2 / ‖c • FactorTwo.rowVectorize v‖^2 =
      UnitaryCovariance.matrixProbability H A v t := by
  rw [inner_smul_left, norm_mul, Complex.norm_conj, norm_smul, mul_pow, mul_pow]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))]
  exact raw_probability H A v hH t

lemma diagonal_commutator (E : ι → ℝ) :
    FactorTwo.commutator (hamiltonian E) = OperatorBridge.liouvillian E := by
  ext A i j
  exact congrFun (congrFun (OperatorBridge.liouvillian_commutator E A).symm i) j

lemma normalized_root {ρ : Operator ι} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    normalizedSeed hρ.sqrt = FactorTwo.rowVectorize hρ.sqrt := by
  have h := PurificationBranches.seed_unit hρ htr
  change ‖FactorTwo.rowVectorize hρ.sqrt‖ = 1 at h
  simp [normalizedSeed,h]

lemma spread_eq_normalized {H ρ : Operator ι} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) (t : ℝ) :
    PurificationBranches.spread (PurificationBranches.generatorU H)
      (PurificationBranches.seed hρ) t =
      PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian H)
        (normalizedSeed hρ.sqrt) t := by
  rw [PhysicalCurvatureNecessary.spread_actual hH hρ t, normalized_root hρ htr]

lemma pure_eq_normalized {n : ℕ} {H ρ : Operator (Fin n)} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) (t : ℝ) :
    PurificationBranches.pureOperator (PurificationBranches.generatorI H)
      (PurificationBranches.seed hρ) t =
      PerturbedDynamics.actualComplexity
        (PerturbedDynamics.liouvillian (PurificationBranches.generatorI H))
        (normalizedSeed (Purification.pureSeed hρ.sqrt)) t := by
  have hu := PureShortTime.pureVector_unit (PurificationBranches.seed hρ)
    (PurificationBranches.seed_unit hρ htr)
  have he : FactorTwo.pureSeed (PurificationBranches.seed hρ) =
      Purification.pureSeed hρ.sqrt := by
    ext ⟨i,j⟩ ⟨k,l⟩
    rfl
  rw [he] at hu
  rw [normalizedSeed,hu]
  simp only [inv_one,Complex.ofReal_one,one_smul]
  rw [← he,PureShortTime.operatorComplexity_physical _
    (PurificationBranches.generatorI_hermitian hH)]
  rfl

def polynomialMap (H A : Operator ι) :
    Polynomial ℂ →ₗ[ℂ] EuclideanSpace ℂ (ι×ι) where
  toFun p := ((‖FactorTwo.rowVectorize A‖⁻¹ : ℝ) : ℂ) •
    FactorTwo.rowVectorize ((Polynomial.aeval (FactorTwo.commutator H)) p A)
  map_add' p q := by simp [map_add,smul_add]
  map_smul' c p := by
    simp [map_smul,smul_smul,mul_comm]

lemma polynomialMap_power (H A : Operator ι) (n : ℕ) :
    polynomialMap H A (Polynomial.X^n) =
      PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian H)
        (normalizedSeed A) n := by
  simp [polynomialMap,PerturbedDynamics.powerSequence,normalizedSeed,
    map_smul,PerturbedDynamics.liouvillian_power_rowVectorize]

end
end Krylov.MatrixGSBridge
