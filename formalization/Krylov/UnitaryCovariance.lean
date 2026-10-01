import Krylov.ConcreteChains

/-! Unitary basis covariance of the actual commutator, matrix exponential,
Hilbert--Schmidt amplitudes and normalized operator-chain probabilities. -/
namespace Krylov.UnitaryCovariance
open Matrix OperatorBridge ConcreteChains
open scoped BigOperators ComplexOrder
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def changeBasis (Q A : Operator ι) : Operator ι := Qᴴ * A * Q

theorem hsInner_eq_trace (A B : Operator ι) : hsInner A B = trace (Aᴴ * B) := by
  simp only [hsInner, trace, mul_apply, conjTranspose_apply]
  exact Finset.sum_comm

theorem changeBasis_mul (Q A B : Operator ι) (hQ : Q * Qᴴ = 1) :
    changeBasis Q (A * B) = changeBasis Q A * changeBasis Q B := by
  unfold changeBasis
  simp only [mul_assoc, ← mul_assoc Q Qᴴ, hQ, one_mul]

theorem changeBasis_sub (Q A B : Operator ι) :
    changeBasis Q (A-B) = changeBasis Q A - changeBasis Q B := by
  simp [changeBasis, mul_sub, sub_mul]

theorem changeBasis_commutator (Q H A : Operator ι) (hQ : Q * Qᴴ = 1) :
    changeBasis Q (H*A-A*H) =
      changeBasis Q H * changeBasis Q A - changeBasis Q A * changeBasis Q H := by
  rw [changeBasis_sub, changeBasis_mul Q H A hQ, changeBasis_mul Q A H hQ]

theorem changeBasis_conjTranspose (Q A : Operator ι) :
    (changeBasis Q A)ᴴ = changeBasis Q Aᴴ := by
  simp [changeBasis, conjTranspose_mul, mul_assoc]

theorem hsInner_changeBasis (Q A B : Operator ι) (hQ : Q * Qᴴ = 1) :
    hsInner (changeBasis Q A) (changeBasis Q B) = hsInner A B := by
  rw [hsInner_eq_trace, hsInner_eq_trace, changeBasis_conjTranspose,
    ← changeBasis_mul Q Aᴴ B hQ]
  unfold changeBasis
  rw [trace_mul_cycle, hQ, one_mul]

theorem isUnit_of_unitary (Q : Operator ι) (hQ : Qᴴ * Q = 1) : IsUnit Q := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  have hh := congrArg (fun z => Qᴴ *ᵥ z) h
  simpa only [mulVec_mulVec, hQ, one_mulVec] using hh

theorem exp_changeBasis (Q A : Operator ι) (hQ : Qᴴ * Q = 1) :
    NormedSpace.exp ℂ (changeBasis Q A) = changeBasis Q (NormedSpace.exp ℂ A) := by
  have hi : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv hQ
  simpa [changeBasis, hi] using Matrix.exp_conj' ℂ Q A (isUnit_of_unitary Q hQ)

theorem changeBasis_smul (Q A : Operator ι) (c : ℂ) :
    changeBasis Q (c • A) = c • changeBasis Q A := by
  simp [changeBasis, Matrix.mul_smul, Matrix.smul_mul]

def evolution (H A : Operator ι) (t : ℝ) : Operator ι :=
  let U := NormedSpace.exp ℂ ((((-t : ℝ) : ℂ) * Complex.I) • H)
  U * A * Uᴴ

theorem evolution_changeBasis (Q H A : Operator ι) (t : ℝ)
    (hQ : Qᴴ * Q = 1) (hQ' : Q * Qᴴ = 1) :
    evolution (changeBasis Q H) (changeBasis Q A) t = changeBasis Q (evolution H A t) := by
  unfold evolution
  rw [← changeBasis_smul, exp_changeBasis Q _ hQ]
  dsimp only
  rw [changeBasis_conjTranspose, ← changeBasis_mul _ _ _ hQ', ← changeBasis_mul _ _ _ hQ']

def matrixProbability (H A v : Operator ι) (t : ℝ) : ℝ :=
  Complex.normSq (hsInner v (evolution H A t)) / ((hsInner A A).re * (hsInner v v).re)

theorem matrixProbability_changeBasis (Q H A v : Operator ι) (t : ℝ)
    (hQ : Qᴴ * Q = 1) (hQ' : Q * Qᴴ = 1) :
    matrixProbability (changeBasis Q H) (changeBasis Q A) (changeBasis Q v) t =
      matrixProbability H A v t := by
  simp only [matrixProbability, evolution_changeBasis Q H A t hQ hQ',
    hsInner_changeBasis Q _ _ hQ']

theorem diagonal_probability (E : ι → ℝ) (A v : Operator ι) (t : ℝ) :
    matrixProbability (hamiltonian E) A v t = chainProbability E A v t := by
  simp only [matrixProbability, evolution, ← diagonalUnitary_eq_exp, chainProbability]

/-- Scalar extension respects real matrix multiplication. -/
theorem complexify_mul (A B : Matrix ι ι ℝ) :
    (A*B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

theorem complexify_transpose (A : Matrix ι ι ℝ) :
    Aᵀ.map Complex.ofReal = (A.map Complex.ofReal)ᴴ := by
  ext i j; simp

/-- Real positive definiteness remains positive definiteness on the complex Hilbert space. -/
theorem complexify_posDef (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    (A.map Complex.ofReal).PosDef := by
  let B := hA.posSemidef.sqrt
  have hBherm : Bᵀ = B := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.posSemidef.posSemidef_sqrt.isHermitian
  have hBsq : B * B = A := hA.posSemidef.sqrt_mul_self
  have hBunit : IsUnit B := by
    apply (isUnit_pow_iff (by norm_num : (2:ℕ) ≠ 0)).mp
    rw [pow_two, hBsq]
    exact hA.isUnit
  have hCBunit : IsUnit (B.map Complex.ofReal) :=
    hBunit.map Complex.ofRealHom.mapMatrix
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hCBunit
  have hp := (Matrix.PosDef.one : (1 : Operator ι).PosDef).conjTranspose_mul_mul_same hinj
  have he : (B.map Complex.ofReal)ᴴ * 1 * B.map Complex.ofReal = A.map Complex.ofReal := by
    rw [mul_one, ← complexify_transpose, hBherm, ← complexify_mul, hBsq]
  rwa [he] at hp

theorem complex_rhoL_posDef : (States.rhoL.map Complex.ofReal).PosDef :=
  complexify_posDef _ States.rhoL_posDef

theorem complex_rhoR_posDef : (States.rhoR.map Complex.ofReal).PosDef :=
  complexify_posDef _ States.rhoR_posDef

theorem complex_rootL_canonical : States.rootL.map Complex.ofReal =
    complex_rhoL_posDef.posSemidef.sqrt := by
  apply (complexify_posDef _ States.rootL_posDef).posSemidef.eq_sqrt_of_sq_eq
  rw [pow_two, ← complexify_mul, States.rootL_square]

theorem complex_rootR_canonical : States.rootR.map Complex.ofReal =
    complex_rhoR_posDef.posSemidef.sqrt := by
  apply (complexify_posDef _ States.rootR_posDef).posSemidef.eq_sqrt_of_sq_eq
  rw [pow_two, ← complexify_mul, States.rootR_square]

def rightBasis : Operator (Fin 3) := States.energyBasisR.map Complex.ofReal

theorem rightBasis_unitary : rightBasisᴴ * rightBasis = 1 := by
  rw [rightBasis, ← complexify_transpose, ← complexify_mul, States.energyBasisR_orthogonal]
  simp

theorem rightBasis_unitary_reverse : rightBasis * rightBasisᴴ = 1 := by
  rw [rightBasis, ← complexify_transpose, ← complexify_mul, States.energyBasisR_orthogonal_reverse]
  simp

theorem right_hamiltonian_coordinates :
    changeBasis rightBasis (States.hR.map Complex.ofReal) = hamiltonian States.energyR := by
  unfold changeBasis rightBasis
  rw [← complexify_transpose, ← complexify_mul, ← complexify_mul, States.hR_energy_basis]
  simp [hamiltonian, Matrix.diagonal_map]

theorem right_density_coordinates :
    changeBasis rightBasis (States.rhoR.map Complex.ofReal) = ConcreteChains.RightMixed.seed := by
  unfold changeBasis rightBasis ConcreteChains.RightMixed.seed
  rw [← complexify_transpose, ← complexify_mul, ← complexify_mul, States.rhoR_energy_basis]

theorem changeBasis_inverse (Q A : Operator ι) (hQ : Qᴴ * Q = 1) :
    changeBasis Q (changeBasis Qᴴ A) = A := by
  simp only [changeBasis, conjTranspose_conjTranspose, mul_assoc,
    ← mul_assoc Qᴴ Q, hQ, one_mul, mul_one]

def rightOriginalChain (k : Fin 3) : Operator (Fin 3) :=
  changeBasis rightBasisᴴ (ConcreteChains.RightMixed.chain k)

theorem right_original_probability (k : Fin 3) (t : ℝ) :
    matrixProbability (States.hR.map Complex.ofReal) (States.rhoR.map Complex.ofReal)
      (rightOriginalChain k) t =
        chainProbability States.energyR ConcreteChains.RightMixed.seed (ConcreteChains.RightMixed.chain k) t := by
  rw [← matrixProbability_changeBasis rightBasis _ _ _ t rightBasis_unitary rightBasis_unitary_reverse]
  rw [right_hamiltonian_coordinates, right_density_coordinates, rightOriginalChain,
    changeBasis_inverse _ _ rightBasis_unitary, diagonal_probability]

theorem right_original_complexity :
    (∑ k : Fin 3, (k.val : ℝ) * matrixProbability (States.hR.map Complex.ofReal)
      (States.rhoR.map Complex.ofReal) (rightOriginalChain k) (Real.pi/3)) = 1141425/913952 := by
  simp_rw [right_original_probability]
  exact ConcreteChains.RightMixed.exact_complexity

end
end Krylov.UnitaryCovariance
