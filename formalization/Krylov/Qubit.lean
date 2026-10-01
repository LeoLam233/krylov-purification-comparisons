import Mathlib

/-!
# Scalar qubit hierarchy and the three-atom formula

These theorems formalize the real-variable part of the qubit hierarchy. The
quantities `muS`, `muK`, and `muI` are the displayed scalar coefficients in the
paper. The actual three-site Jacobi matrix exponential is also derived. No
theorem here identifies the original physical-qubit Krylov constructions with
these scalar parameterizations; that requires the independent spectral-measure
and Lanczos bridges.
-/

namespace Krylov.Qubit

noncomputable section

set_option maxHeartbeats 2000000

/-- Complexity formula for the symmetric three-atom chain. -/
def threeAtom (μ t : ℝ) : ℝ :=
  μ * Real.sin t ^ 2 + 8 * μ * (1 - μ) * Real.sin (t / 2) ^ 4

/-- Spread coefficient for the canonical time-dependent qubit purification. -/
def muS (z c : ℝ) : ℝ := (1 - Real.sqrt (1 - z)) * (1 - c) / 2

/-- Normalized mixed-operator qubit coefficient. -/
def muK (z c : ℝ) : ℝ := z * (1 - c) / (1 + z)

/-- Time-independent rank-one purified-operator qubit coefficient. -/
def muI (z c : ℝ) : ℝ := (1 - z * c) / 2

private theorem sqrt_bounds {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ Real.sqrt (1 - z) ∧ Real.sqrt (1 - z) ≤ 1 ∧
      1 - Real.sqrt (1 - z) ≤ z := by
  have hs0 := Real.sqrt_nonneg (1 - z)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 - z by linarith)
  have hs1 : Real.sqrt (1 - z) ≤ 1 := by nlinarith
  refine ⟨hs0, hs1, ?_⟩
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]

/-- All three qubit coefficients are in the monotonicity interval, including
pure and maximally mixed states and a commuting eigenbasis. -/
theorem coefficient_bounds {z c : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    muS z c ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
    muK z c ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
    muI z c ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have hz0 := hz.1
  have hz1 := hz.2
  have hc0 := hc.1
  have hc1 := hc.2
  obtain ⟨hs0, hs1, _⟩ := sqrt_bounds hz.1 hz.2
  have hsm : 0 ≤ 1 - Real.sqrt (1 - z) := sub_nonneg.mpr hs1
  have hcm : 0 ≤ 1 - c := sub_nonneg.mpr hc.2
  have hSprod : (1 - Real.sqrt (1 - z)) * (1 - c) ≤ 1 := by
    nlinarith [mul_nonneg hs0 hcm]
  have hzc0 : 0 ≤ z * c := mul_nonneg hz.1 hc.1
  have hzc1 : z * c ≤ 1 := by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hc.2)]
  have hden : 0 < 1 + z := by linarith [hz.1]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · unfold muS
    positivity
  · unfold muS
    linarith
  · unfold muK
    positivity
  · unfold muK
    apply (div_le_iff₀ hden).2
    nlinarith
  · unfold muI
    linarith
  · unfold muI
    linarith

/-- The parameter ordering is established without division by `muS`; therefore
its zero endpoints are included rather than handled by a nonzero hypothesis. -/
theorem coefficient_order {z c : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) : muS z c ≤ muK z c ∧ muK z c ≤ muI z c := by
  have hz0 := hz.1
  have hz1 := hz.2
  have hc0 := hc.1
  have hc1 := hc.2
  obtain ⟨hs0, hs1, hsz⟩ := sqrt_bounds hz.1 hz.2
  have hden : 0 < 1 + z := by linarith [hz.1]
  constructor
  · calc
      muS z c ≤ z * (1 - c) / 2 := by
        unfold muS
        nlinarith [mul_nonneg (sub_nonneg.mpr hsz) (sub_nonneg.mpr hc.2)]
      _ ≤ muK z c := by
        unfold muK
        apply (le_div_iff₀ hden).2
        nlinarith [mul_nonneg (mul_nonneg hz.1 (sub_nonneg.mpr hc.2))
          (sub_nonneg.mpr hz.2)]
  · unfold muK muI
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) (mul_nonneg hz.1 hc.1)]

/-- Exact algebraic difference, valid for every pair of real parameters. -/
theorem threeAtom_sub (u v t : ℝ) :
    threeAtom v t - threeAtom u t =
      (v - u) * (Real.sin t ^ 2 + 8 * (1 - u - v) * Real.sin (t / 2) ^ 4) := by
  unfold threeAtom
  ring

/-- Monotonicity is proved by a nonnegative difference, without differentiating
and without excluding the endpoints of the interval. -/
theorem threeAtom_mono {u v : ℝ} (hu : u ≤ (1 : ℝ) / 2)
    (hv : v ≤ (1 : ℝ) / 2) (huv : u ≤ v) (t : ℝ) :
    threeAtom u t ≤ threeAtom v t := by
  have hfac : 0 ≤ 1 - u - v := by linarith
  have hbr : 0 ≤ Real.sin t ^ 2 + 8 * (1 - u - v) * Real.sin (t / 2) ^ 4 := by
    positivity
  have hd := mul_nonneg (sub_nonneg.mpr huv) hbr
  rw [← threeAtom_sub] at hd
  linarith

/-- Scalar qubit hierarchy for all real times and all closed-interval
parameters. This is a scalar theorem; it does not assert the physical-matrix
spectral reduction to these parameterizations. -/
theorem hierarchy {z c : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    threeAtom (muS z c) t ≤ threeAtom (muK z c) t ∧
      threeAtom (muK z c) t ≤ threeAtom (muI z c) t := by
  obtain ⟨hS, hK, hI⟩ := coefficient_bounds hz hc
  obtain ⟨hSK, hKI⟩ := coefficient_order hz hc
  exact ⟨threeAtom_mono hS.2 hK.2 hSK t, threeAtom_mono hK.2 hI.2 hKI t⟩

/-- A frequency gap, including a zero or negative gap, only changes the time
argument in the scalar hierarchy. -/
theorem hierarchy_with_gap {z c : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (ω t : ℝ) :
    threeAtom (muS z c) (ω * t) ≤ threeAtom (muK z c) (ω * t) ∧
      threeAtom (muK z c) (ω * t) ≤ threeAtom (muI z c) (ω * t) :=
  hierarchy hz hc (ω * t)

@[simp] theorem threeAtom_zero_parameter (t : ℝ) : threeAtom 0 t = 0 := by
  simp [threeAtom]

@[simp] theorem threeAtom_one_parameter (t : ℝ) : threeAtom 1 t = Real.sin t ^ 2 := by
  simp [threeAtom]

@[simp] theorem threeAtom_zero_time (μ : ℝ) : threeAtom μ 0 = 0 := by
  simp [threeAtom]

@[simp] theorem muS_pure (c : ℝ) : muS 1 c = (1 - c) / 2 := by simp [muS]
@[simp] theorem muK_pure (c : ℝ) : muK 1 c = (1 - c) / 2 := by norm_num [muK]
@[simp] theorem muI_pure (c : ℝ) : muI 1 c = (1 - c) / 2 := by simp [muI]
@[simp] theorem muS_mixed (c : ℝ) : muS 0 c = 0 := by simp [muS]
@[simp] theorem muK_mixed (c : ℝ) : muK 0 c = 0 := by simp [muK]
@[simp] theorem muI_mixed (c : ℝ) : muI 0 c = 1 / 2 := by simp [muI]
@[simp] theorem muS_commuting (z : ℝ) : muS z 1 = 0 := by simp [muS]
@[simp] theorem muK_commuting (z : ℝ) : muK z 1 = 0 := by simp [muK]
@[simp] theorem muI_commuting (z : ℝ) : muI z 1 = (1 - z) / 2 := by simp [muI]

/-- Real squared-amplitude expressions associated with the displayed
three-atom evolution. -/
def prob0 (μ t : ℝ) : ℝ := (1 - μ + μ * Real.cos t) ^ 2
def prob1 (μ t : ℝ) : ℝ := μ * Real.sin t ^ 2
def prob2 (μ t : ℝ) : ℝ := μ * (1 - μ) * (Real.cos t - 1) ^ 2

/-- These expressions are a probability vector for every `0 ≤ μ ≤ 1`. -/
theorem probabilities_nonnegative {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    0 ≤ prob0 μ t ∧ 0 ≤ prob1 μ t ∧ 0 ≤ prob2 μ t := by
  unfold prob0 prob1 prob2
  exact ⟨sq_nonneg _, mul_nonneg hμ.1 (sq_nonneg _),
    mul_nonneg (mul_nonneg hμ.1 (sub_nonneg.mpr hμ.2)) (sq_nonneg _)⟩

/-- Probability conservation is an exact trigonometric identity; the algebra
also holds outside the probability-parameter interval. -/
theorem probabilities_sum (μ t : ℝ) : prob0 μ t + prob1 μ t + prob2 μ t = 1 := by
  have hsin : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  unfold prob0 prob1 prob2
  rw [hsin]
  ring

/-- The index-weighted sum of the displayed probability vector is exactly the
three-atom complexity formula. -/
theorem weighted_probabilities (μ t : ℝ) : prob1 μ t + 2 * prob2 μ t = threeAtom μ t := by
  have hhalf : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (t / 2) using 1
    congr 1
    ring
  have htrig := Real.sin_sq_add_cos_sq (t / 2)
  have hcos : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    nlinarith
  unfold prob1 prob2 threeAtom
  rw [hcos]
  ring

/-- The square-root coefficient used above follows from nonnegative density
matrix eigenvalues of total mass one. This is an eigenvalue identity, not an
unproved assertion of matrix spectral reduction. -/
theorem eigenvalue_sqrt_bridge {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsum : p + q = 1) :
    (Real.sqrt p - Real.sqrt q) ^ 2 = 1 - Real.sqrt (1 - (p - q) ^ 2) := by
  have hpq : 0 ≤ p * q := mul_nonneg hp hq
  have hrad : 1 - (p - q) ^ 2 = 4 * (p * q) := by
    calc
      1 - (p - q) ^ 2 = (p + q) ^ 2 - (p - q) ^ 2 := by rw [hsum]; ring
      _ = 4 * (p * q) := by ring
  have hsq : (2 * (Real.sqrt p * Real.sqrt q)) ^ 2 = 4 * (p * q) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq]
    ring
  have hsqrt : Real.sqrt (1 - (p - q) ^ 2) = 2 * (Real.sqrt p * Real.sqrt q) := by
    apply (Real.sqrt_eq_iff_eq_sq (by rw [hrad]; positivity) (by positivity)).2
    rw [hsq, hrad]
  rw [hsqrt]
  nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hq]

/-- The eigenvalue contrast of a qubit density matrix is a valid scalar
parameter for `hierarchy`. -/
theorem eigenvalue_contrast_bounds {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsum : p + q = 1) : (p - q) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact sq_nonneg _
  · nlinarith [mul_nonneg hp hq, congrArg (fun x : ℝ => x ^ 2) hsum]

open Matrix

/-- Three-site Jacobi matrix with arbitrary couplings. -/
def jacobi (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, a, 0; a, 0, b; 0, b, 0]

/-- The exact cubic relation underlying the three-atom evolution. -/
theorem jacobi_cube {a b : ℂ} (h : a ^ 2 + b ^ 2 = 1) :
    jacobi a b ^ 3 = jacobi a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jacobi, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | (solve | ring) | (solve | linear_combination a * h) | linear_combination b * h

private def eigenvectors (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-a, b, a; 1, 0, 1; -b, -a, b]

private def eigenvectorsInv (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-a / 2, 1 / 2, -b / 2; b, 0, -a; a / 2, 1 / 2, b / 2]

private theorem eigenvectors_mul_inv {a b : ℂ} (h : a ^ 2 + b ^ 2 = 1) :
    eigenvectors a b * eigenvectorsInv a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenvectors, eigenvectorsInv, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | (solve | ring) | linear_combination h

private theorem eigenvectors_inv_mul {a b : ℂ} (h : a ^ 2 + b ^ 2 = 1) :
    eigenvectorsInv a b * eigenvectors a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenvectors, eigenvectorsInv, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | (solve | ring) | (solve | linear_combination h) | (solve | linear_combination h / 2) | linear_combination -h / 2

private def eigenvectorUnit {a b : ℂ} (h : a ^ 2 + b ^ 2 = 1) :
    (Matrix (Fin 3) (Fin 3) ℂ)ˣ where
  val := eigenvectors a b
  inv := eigenvectorsInv a b
  val_inv := eigenvectors_mul_inv h
  inv_val := eigenvectors_inv_mul h

private theorem diagonalization (a b t : ℂ) :
    eigenvectors a b * Matrix.diagonal ![t * Complex.I, 0, -(t * Complex.I)] *
      eigenvectorsInv a b = (-(t * Complex.I)) • jacobi a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenvectors, eigenvectorsInv, jacobi, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.diagonal, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Actual matrix-exponential evolution of the first basis vector, computed by
explicit diagonalization. `a` and `b` may vanish, so terminated endpoint
chains are included. -/
theorem jacobi_exp_first_column {a b : ℂ} (h : a ^ 2 + b ^ 2 = 1) (t : ℝ) :
    (fun i => NormedSpace.exp ℂ ((-((t : ℂ) * Complex.I)) • jacobi a b) i 0) =
      ![b ^ 2 + a ^ 2 * (Real.cos t : ℂ),
        -Complex.I * a * (Real.sin t : ℂ),
        a * b * ((Real.cos t : ℂ) - 1)] := by
  let U := eigenvectorUnit h
  have hd : (↑U : Matrix (Fin 3) (Fin 3) ℂ) *
      Matrix.diagonal ![(t : ℂ) * Complex.I, 0, -((t : ℂ) * Complex.I)] * (↑(U⁻¹) : Matrix (Fin 3) (Fin 3) ℂ) =
      (-((t : ℂ) * Complex.I)) • jacobi a b := diagonalization a b t
  rw [← hd, Matrix.exp_units_conj, Matrix.exp_diagonal]
  have hp : Complex.exp ((t : ℂ) * Complex.I) =
      (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hn : Complex.exp (-((t : ℂ) * Complex.I)) =
      (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I := by
    rw [show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp [sub_eq_add_neg]
  ext i
  fin_cases i <;>
    simp [U, eigenvectorUnit, eigenvectors, eigenvectorsInv, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ,
      hp, hn] <;>
    ring

/-- Jacobi matrix of the symmetric three-atom probability measure. -/
def threeAtomJacobi (μ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  jacobi (Real.sqrt μ) (Real.sqrt (1 - μ))

/-- Exact amplitudes, including zero-coupling endpoints. -/
def amplitudes (μ t : ℝ) : Fin 3 → ℂ :=
  ![((1 - μ + μ * Real.cos t : ℝ) : ℂ),
    -Complex.I * (Real.sqrt μ : ℂ) * (Real.sin t : ℂ),
    ((Real.sqrt (μ * (1 - μ)) * (Real.cos t - 1) : ℝ) : ℂ)]

/-- The advertised amplitudes are the actual first column of the matrix
exponential, rather than only an abstract probability ansatz. -/
theorem threeAtom_exp_amplitudes {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    (fun i => NormedSpace.exp ℂ ((-((t : ℂ) * Complex.I)) • threeAtomJacobi μ) i 0) =
      amplitudes μ t := by
  have ha : (Real.sqrt μ : ℂ) ^ 2 = (μ : ℂ) := by
    exact_mod_cast Real.sq_sqrt hμ.1
  have hb : (Real.sqrt (1 - μ) : ℂ) ^ 2 = ((1 - μ : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hμ.2)
  have hab : (Real.sqrt μ : ℂ) ^ 2 + (Real.sqrt (1 - μ) : ℂ) ^ 2 = 1 := by
    rw [ha, hb]
    push_cast
    ring
  have hcol := jacobi_exp_first_column hab t
  unfold threeAtomJacobi
  rw [hcol]
  ext i
  fin_cases i <;> simp [amplitudes, ha, hb, Real.sqrt_mul hμ.1]

/-- The squared norms of the actual evolution amplitudes are the three
probabilities appearing in the complexity calculation. -/
theorem amplitudes_normSq {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    Complex.normSq (amplitudes μ t 0) = prob0 μ t ∧
    Complex.normSq (amplitudes μ t 1) = prob1 μ t ∧
    Complex.normSq (amplitudes μ t 2) = prob2 μ t := by
  have hm : 0 ≤ μ * (1 - μ) := mul_nonneg hμ.1 (sub_nonneg.mpr hμ.2)
  constructor
  · change Complex.normSq (((1 - μ + μ * Real.cos t : ℝ)) : ℂ) = prob0 μ t
    rw [Complex.normSq_ofReal]
    simp only [prob0, pow_two]
  constructor
  · change Complex.normSq (-Complex.I * (Real.sqrt μ : ℂ) * (Real.sin t : ℂ)) = prob1 μ t
    rw [Complex.normSq_mul, Complex.normSq_mul]
    simp only [Complex.normSq_neg, Complex.normSq_I, Complex.normSq_ofReal, one_mul,
      ← pow_two, Real.sq_sqrt hμ.1, prob1]
  · change Complex.normSq (((Real.sqrt (μ * (1 - μ)) * (Real.cos t - 1) : ℝ)) : ℂ) = prob2 μ t
    rw [Complex.normSq_ofReal, ← pow_two, mul_pow, Real.sq_sqrt hm]
    rfl

/-- Full three-site scalar chain complexity, defined from its genuine matrix
exponential and standard basis. At `μ = 0` or `μ = 1`, the extra zero-coupling
coordinates have zero probability, so this equals the terminated-chain value. -/
def matrixChainComplexity (μ t : ℝ) : ℝ :=
  ∑ i : Fin 3, (i.val : ℝ) *
    ‖NormedSpace.exp ℂ ((-((t : ℂ) * Complex.I)) • threeAtomJacobi μ) i 0‖ ^ 2

/-- An actual matrix-exponential-to-formula theorem for the three-atom chain.
This still does not replace the separate physical-qubit spectral reduction. -/
theorem matrixChainComplexity_eq {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    matrixChainComplexity μ t = threeAtom μ t := by
  have he := threeAtom_exp_amplitudes hμ t
  obtain ⟨h0, h1, h2⟩ := amplitudes_normSq hμ t
  unfold matrixChainComplexity
  simp_rw [← Complex.normSq_eq_norm_sq]
  simp_rw [congrFun he]
  norm_num [Fin.sum_univ_succ, h1, h2]
  exact weighted_probabilities μ t

/-- Polynomial form used by the rational certificate and ratio modules, with
`x = sin²(t/2)`. -/
theorem threeAtom_polynomial (μ t : ℝ) :
    threeAtom μ t = 4 * μ * (Real.sin (t / 2) ^ 2) *
      (1 + (1 - 2 * μ) * (Real.sin (t / 2) ^ 2)) := by
  have hsin : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    convert Real.sin_two_mul (t / 2) using 1
    congr 1
    ring
  have hcos : Real.cos (t / 2) ^ 2 = 1 - Real.sin (t / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  unfold threeAtom
  rw [hsin, mul_pow, mul_pow, hcos]
  ring

@[simp] theorem threeAtom_half (t : ℝ) :
    threeAtom (1 / 2) t = 2 * Real.sin (t / 2) ^ 2 := by
  rw [threeAtom_polynomial]
  ring

/-- A trigonometric rotation parameter always lies in the required closed
interval. -/
theorem cosine_parameter_bounds (θ : ℝ) : Real.cos θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨sq_nonneg _, by nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]⟩

/-- Scalar hierarchy specialized to density eigenvalues, a rotation angle,
and arbitrary energy difference and time. -/
theorem hierarchy_eigenvalues {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsum : p + q = 1) (θ E₁ E₂ t : ℝ) :
    threeAtom (muS ((p - q) ^ 2) (Real.cos θ ^ 2)) ((E₂ - E₁) * t) ≤
        threeAtom (muK ((p - q) ^ 2) (Real.cos θ ^ 2)) ((E₂ - E₁) * t) ∧
    threeAtom (muK ((p - q) ^ 2) (Real.cos θ ^ 2)) ((E₂ - E₁) * t) ≤
        threeAtom (muI ((p - q) ^ 2) (Real.cos θ ^ 2)) ((E₂ - E₁) * t) :=
  hierarchy (eigenvalue_contrast_bounds hp hq hsum) (cosine_parameter_bounds θ) _

/-- The concrete three-atom Jacobi generator is Hermitian for every real
parameter (even before restricting the square-root arguments). -/
theorem threeAtomJacobi_hermitian (μ : ℝ) : (threeAtomJacobi μ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeAtomJacobi, jacobi, Matrix.conjTranspose_apply]

/-- Probability conservation for the genuine matrix exponential. -/
theorem matrix_evolution_normalized {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    (∑ i : Fin 3,
      ‖NormedSpace.exp ℂ ((-((t : ℂ) * Complex.I)) • threeAtomJacobi μ) i 0‖ ^ 2) = 1 := by
  have he := threeAtom_exp_amplitudes hμ t
  obtain ⟨h0, h1, h2⟩ := amplitudes_normSq hμ t
  simp_rw [← Complex.normSq_eq_norm_sq, congrFun he]
  simpa [Fin.sum_univ_succ, h0, h1, h2, add_assoc] using probabilities_sum μ t

/-- A matrix-exponential hierarchy for the three concrete Jacobi chains
obtained from the qubit scalar parameters. Identifying these with the original
physical qubit Krylov constructions remains a separate reduction theorem. -/
theorem matrix_chain_hierarchy {z c : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    matrixChainComplexity (muS z c) t ≤ matrixChainComplexity (muK z c) t ∧
      matrixChainComplexity (muK z c) t ≤ matrixChainComplexity (muI z c) t := by
  obtain ⟨hS, hK, hI⟩ := coefficient_bounds hz hc
  have hS' : muS z c ∈ Set.Icc (0 : ℝ) 1 := ⟨hS.1, by linarith [hS.2]⟩
  have hK' : muK z c ∈ Set.Icc (0 : ℝ) 1 := ⟨hK.1, by linarith [hK.2]⟩
  have hI' : muI z c ∈ Set.Icc (0 : ℝ) 1 := ⟨hI.1, by linarith [hI.2]⟩
  rw [matrixChainComplexity_eq hS', matrixChainComplexity_eq hK', matrixChainComplexity_eq hI']
  exact hierarchy hz hc t

/-- Standard coordinate vector in the three-site chain. -/
def basisVector (j : Fin 3) : Fin 3 → ℂ := (1 : Matrix (Fin 3) (Fin 3) ℂ) j

/-- Orthonormality in the Hermitian coordinate inner product. -/
theorem basisVector_gram (i j : Fin 3) :
    (∑ k : Fin 3, star (basisVector i k) * basisVector j k) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [basisVector, Matrix.one_apply, Fin.sum_univ_succ]

/-- First Lanczos recurrence with zero diagonal coefficient. -/
theorem jacobi_lanczos_zero (a b : ℂ) :
    jacobi a b *ᵥ basisVector 0 = a • basisVector 1 := by
  ext i
  fin_cases i <;>
    simp [jacobi, basisVector, Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Middle Lanczos recurrence with zero diagonal coefficient. -/
theorem jacobi_lanczos_one (a b : ℂ) :
    jacobi a b *ᵥ basisVector 1 = a • basisVector 0 + b • basisVector 2 := by
  ext i
  fin_cases i <;>
    simp [jacobi, basisVector, Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Last recurrence certifies exact termination after the third vector. -/
theorem jacobi_lanczos_two (a b : ℂ) :
    jacobi a b *ᵥ basisVector 2 = b • basisVector 1 := by
  ext i
  fin_cases i <;>
    simp [jacobi, basisVector, Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Columns are the first three genuine Krylov vectors, before orthogonalization. -/
def krylovPowers (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ((jacobi a b ^ j.val) *ᵥ basisVector 0) i

/-- Triangular shape of the Krylov power matrix. -/
theorem krylovPowers_eq (a b : ℂ) :
    krylovPowers a b = !![1, 0, a ^ 2; 0, a, 0; 0, 0, a * b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [krylovPowers, jacobi, basisVector, Matrix.one_apply, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]
  all_goals ring

theorem krylovPowers_det (a b : ℂ) : (krylovPowers a b).det = a ^ 2 * b := by
  rw [krylovPowers_eq]
  simp [Matrix.det_fin_three]
  ring

/-- Nonzero couplings make the first three Krylov powers independent. Together
with the recurrences, this certifies the cyclic basis; the positive-real
couplings used by `threeAtomJacobi` also give the usual Lanczos convention. -/
theorem krylovPowers_independent {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℂ (krylovPowers a b).col := by
  apply Matrix.linearIndependent_cols_of_det_ne_zero
  rw [krylovPowers_det]
  exact mul_ne_zero (pow_ne_zero 2 ha) hb

/-- Strictly interior parameters have a full, exactly three-dimensional cyclic
space, since these three powers lie in it and are independent. -/
theorem threeAtom_krylov_independent {μ : ℝ} (hμ : μ ∈ Set.Ioo (0 : ℝ) 1) :
    LinearIndependent ℂ (krylovPowers (Real.sqrt μ) (Real.sqrt (1 - μ))).col := by
  apply krylovPowers_independent
  · exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hμ.1))
  · exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (show 0 < 1 - μ by linarith [hμ.2])))

/-- The seed is nonzero, including both endpoint chains. -/
theorem basisVector_zero_ne : basisVector 0 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [basisVector, Matrix.one_apply] at h0

/-- At zero weight, the seed already terminates the Krylov chain. -/
theorem endpoint_zero_termination : threeAtomJacobi 0 *ᵥ basisVector 0 = 0 := by
  simpa [threeAtomJacobi] using jacobi_lanczos_zero (0 : ℂ) 1

/-- The two surviving endpoint Krylov vectors are independent. -/
theorem endpoint_one_independent :
    LinearIndependent ℂ ![basisVector 0, basisVector 1] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · simpa [Fin.sum_univ_succ, basisVector, Matrix.one_apply] using congrFun hg (0 : Fin 3)
  · simpa [Fin.sum_univ_succ, basisVector, Matrix.one_apply] using congrFun hg (1 : Fin 3)

/-- At unit weight, exactly the first two coordinates form the terminated
Krylov chain; the third coordinate is decoupled. -/
theorem endpoint_one_termination :
    threeAtomJacobi 1 *ᵥ basisVector 0 = basisVector 1 ∧
    threeAtomJacobi 1 *ᵥ basisVector 1 = basisVector 0 ∧
    threeAtomJacobi 1 *ᵥ basisVector 2 = 0 := by
  constructor
  · simpa [threeAtomJacobi] using jacobi_lanczos_zero (1 : ℂ) 0
  constructor
  · simpa [threeAtomJacobi] using jacobi_lanczos_one (1 : ℂ) 0
  · simpa [threeAtomJacobi] using jacobi_lanczos_two (1 : ℂ) 0

end
end Krylov.Qubit
