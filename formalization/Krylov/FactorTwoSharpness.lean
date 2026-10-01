import Krylov.FactorTwo

/-!
# An exact physical saturating example for the factor-two coefficient

A two-level dynamics embedded with one decoupled spectator uses the actual
matrix exponential and the actual commutator of its rank-one density. Both
Lanczos bases and the operator probabilities are checked directly.
-/
namespace Krylov.FactorTwoSharpness
open Matrix
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

def H : Mat := Qubit.threeAtomJacobi 1

def ψ (t : ℝ) : Fin 3 → ℂ :=
  fun i => NormedSpace.exp ℂ ((-((t : ℂ) * Complex.I)) • H) i 0

def σ (t : ℝ) : Mat := FactorTwo.pureSeed (ψ t)

def q : ℝ := Real.sqrt 2 / 2

def opBasis : Fin 3 → Mat :=
  ![!![1,0,0;0,0,0;0,0,0],
    !![0,-(q : ℂ),0;(q : ℂ),0,0;0,0,0],
    !![0,0,0;0,-1,0;0,0,0]]

def stateComplexity (t : ℝ) : ℝ := Qubit.matrixChainComplexity 1 t

def operatorAmplitude (k : Fin 3) (t : ℝ) : ℂ :=
  ⟪FactorTwo.rowVectorize (opBasis k), FactorTwo.rowVectorize (σ t)⟫_ℂ

def operatorComplexity (t : ℝ) : ℝ :=
  ∑ k : Fin 3, (k.val : ℝ) * ‖operatorAmplitude k t‖ ^ 2

theorem q_sq : q ^ 2 = 1 / 2 := by
  unfold q
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem q_pos : 0 < q := by unfold q; positivity

theorem H_eq : H = !![0,1,0;1,0,0;0,0,0] := by
  simp [H, Qubit.threeAtomJacobi, Qubit.jacobi]

theorem H_hermitian : H.IsHermitian := Qubit.threeAtomJacobi_hermitian 1

/-- The vector comes from the actual Hamiltonian matrix exponential. -/
theorem state_evolution (t : ℝ) :
    ψ t = ![(Real.cos t : ℂ), -Complex.I * (Real.sin t : ℂ), 0] := by
  have h := Qubit.threeAtom_exp_amplitudes (μ := 1) (by constructor <;> norm_num) t
  change (fun i => NormedSpace.exp ℂ ((-((t : ℂ) * Complex.I)) • Qubit.threeAtomJacobi 1) i 0) = _
  rw [h]
  simp [Qubit.amplitudes]

theorem density_evolution (t : ℝ) :
    σ t = !![((Real.cos t ^ 2 : ℝ) : ℂ), Complex.I * ((Real.cos t * Real.sin t : ℝ) : ℂ), 0;
      -Complex.I * ((Real.cos t * Real.sin t : ℝ) : ℂ), ((Real.sin t ^ 2 : ℝ) : ℂ), 0;
      0,0,0] := by
  unfold σ FactorTwo.pureSeed
  rw [state_evolution]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FactorTwo.outer, Complex.star_def, Complex.I_sq, pow_two,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin] <;> ring_nf
  all_goals simp [Complex.I_sq]

/-- The actual evolving state has unit norm at every time. -/
theorem state_normalized (t : ℝ) : (∑ i : Fin 3, ‖ψ t i‖ ^ 2) = 1 := by
  exact Qubit.matrix_evolution_normalized (μ := 1) (by constructor <;> norm_num) t

theorem lanczos_coupling_positive : 0 < 2 * q := by have := q_pos; positivity

/-- The operator Lanczos seed is the actual initial rank-one density. -/
theorem operator_seed : opBasis 0 = σ 0 := by
  rw [density_evolution]
  simp [opBasis]

/-- The three operator vectors are genuinely orthonormal in Hilbert--Schmidt
space; in particular none is a fictitious padding coordinate. -/
theorem opBasis_orthonormal :
    Orthonormal ℂ (fun k => FactorTwo.rowVectorize (opBasis k)) := by
  have hq : (q : ℂ) ^ 2 = 1 / 2 := by rw [← Complex.ofReal_pow, q_sq]; norm_num
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [FactorTwo.rowVectorize_inner]
  fin_cases i <;> fin_cases j <;>
    simp [opBasis, Fin.sum_univ_succ, Complex.star_def] <;>
    first | (solve | ring) | linear_combination 2 * hq

/-- Exact Lanczos recurrences with the positive couplings `2q = sqrt 2` and
zero diagonal terms; the third recurrence is exact termination. -/
theorem operator_lanczos :
    FactorTwo.commutator H (opBasis 0) = ((2 * q : ℝ) : ℂ) • opBasis 1 ∧
    FactorTwo.commutator H (opBasis 1) = ((2 * q : ℝ) : ℂ) • opBasis 0 +
      ((2 * q : ℝ) : ℂ) • opBasis 2 ∧
    FactorTwo.commutator H (opBasis 2) = ((2 * q : ℝ) : ℂ) • opBasis 1 := by
  have hq : (q : ℂ) ^ 2 = 1 / 2 := by rw [← Complex.ofReal_pow, q_sq]; norm_num
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [FactorTwo.commutator_apply, H_eq, opBasis, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | (solve | ring) | (solve | linear_combination 2 * hq) | linear_combination -2 * hq

/-- Exact amplitudes in the actual operator Lanczos basis. -/
theorem operator_amplitudes (t : ℝ) :
    (fun k => operatorAmplitude k t) =
      ![((Real.cos t ^ 2 : ℝ) : ℂ),
        -2 * Complex.I * ((q * Real.cos t * Real.sin t : ℝ) : ℂ),
        -((Real.sin t ^ 2 : ℝ) : ℂ)] := by
  ext k
  unfold operatorAmplitude
  rw [FactorTwo.rowVectorize_inner, density_evolution]
  fin_cases k <;> simp [opBasis, Fin.sum_univ_succ, Complex.star_def] <;> ring

/-- Actual state Krylov complexity, with the zero-coupling spectator omitted
or retained with zero probability. -/
theorem state_complexity (t : ℝ) : stateComplexity t = Real.sin t ^ 2 := by
  unfold stateComplexity
  rw [Qubit.matrixChainComplexity_eq (μ := 1) (by constructor <;> norm_num)]
  simp

/-- Exact operator complexity calculated from Hilbert--Schmidt amplitudes. -/
theorem operator_complexity (t : ℝ) : operatorComplexity t = 2 * Real.sin t ^ 2 := by
  have hA := congrFun (operator_amplitudes t)
  unfold operatorComplexity
  simp_rw [← Complex.normSq_eq_norm_sq]
  norm_num [Fin.sum_univ_succ, hA, Complex.normSq_mul, Complex.normSq_ofReal,
    ← pow_two, mul_pow, ← Complex.ofReal_cos, ← Complex.ofReal_sin, q_sq]
  linear_combination 2 * Real.sin t ^ 2 * (Real.sin_sq_add_cos_sq t)

theorem exact_saturation (t : ℝ) : operatorComplexity t = 2 * stateComplexity t := by
  rw [operator_complexity, state_complexity]

/-- A positive-complexity time makes this a nonstationary sharpness witness. -/
theorem nonstationary_witness : stateComplexity (Real.pi / 2) = 1 := by
  rw [state_complexity, Real.sin_pi_div_two]
  norm_num

/-- Every constant larger than two fails on this one normalized finite
physical example at a finite time. -/
theorem excludes_larger_multiplier {c : ℝ} (hc : 2 < c) :
    operatorComplexity (Real.pi / 2) < c * stateComplexity (Real.pi / 2) := by
  rw [exact_saturation, nonstationary_witness]
  nlinarith

end
end Krylov.FactorTwoSharpness
