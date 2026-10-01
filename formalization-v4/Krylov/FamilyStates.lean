import Krylov.Ratios
import Krylov.States
import Krylov.Qubit

/-!
# Physical matrix certificates for parameter families

The qutrit matrix family is positive definite and normalized; its displayed
positive square root and its diagonal-Hamiltonian spectral gap weights are
proved directly in mathlib's matrix definitions.  These facts connect the
scalar weights in `Ratios` to physical input matrices.  A separate general
operator-to-Krylov spectral representation is still needed to identify a
complexity defined by Lanczos iteration with the three-atom formula.
-/

noncomputable section
namespace Krylov.FamilyStates
open Matrix
open scoped BigOperators
open Krylov.Ratios

abbrev Qutrit := Matrix (Fin 3) (Fin 3) ℝ

def qutritNormalization (m : ℝ) : ℝ := m ^ 2 + 5

def qutritRaw (m : ℝ) : Qutrit :=
  !![m^2,0,0;0,5/2,3/2;0,3/2,5/2]

def qutritState (m : ℝ) : Qutrit := (1 / qutritNormalization m) • qutritRaw m

def qutritRootScale (m : ℝ) : ℝ := 1 / (2 * Real.sqrt (qutritNormalization m))

def qutritRoot (m : ℝ) : Qutrit :=
  qutritRootScale m • !![2*m,0,0;0,3,1;0,1,3]

def qutritEnergy : Fin 3 → ℝ := ![2,0,1]
def threeNodes : Fin 3 → ℝ := ![-1,0,1]

private theorem coordinates_sq_pos (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  by_contra hp
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 2)]
  have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  apply hx
  ext i
  fin_cases i <;> simp_all

theorem qutritNormalization_pos (m : ℝ) : 0 < qutritNormalization m := by
  unfold qutritNormalization
  positivity

theorem qutritState_hermitian (m : ℝ) : (qutritState m).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qutritState, qutritRaw, IsHermitian, conjTranspose_apply]

theorem qutritState_trace (m : ℝ) : trace (qutritState m) = 1 := by
  have hn : qutritNormalization m ≠ 0 := ne_of_gt (qutritNormalization_pos m)
  norm_num [trace, qutritState, qutritRaw, Fin.sum_univ_succ]
  unfold qutritNormalization at *
  field_simp
  ring

theorem qutritState_posDef {m : ℝ} (hm : 4 ≤ m) : (qutritState m).PosDef := by
  refine ⟨qutritState_hermitian m, ?_⟩
  intro x hx
  have hp := coordinates_sq_pos x hx
  have hc : 0 ≤ (m ^ 2 - 1) * x 0 ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _)
    nlinarith
  have hbase : 0 < m ^ 2 * x 0 ^ 2 + (5 / 2) * x 1 ^ 2 +
      3 * x 1 * x 2 + (5 / 2) * x 2 ^ 2 := by
    nlinarith [sq_nonneg (x 1 + x 2)]
  have hs : 0 < 1 / qutritNormalization m := by
    exact one_div_pos.mpr (qutritNormalization_pos m)
  have hmul := mul_pos hs hbase
  norm_num [dotProduct, mulVec, qutritState, qutritRaw, Fin.sum_univ_succ]
  convert hmul using 1
  ring

theorem qutritState_full_rank {m : ℝ} (hm : 4 ≤ m) : IsUnit (qutritState m) :=
  (qutritState_posDef hm).isUnit

theorem qutritRootScale_pos (m : ℝ) : 0 < qutritRootScale m := by
  have hn := qutritNormalization_pos m
  unfold qutritRootScale
  positivity

theorem qutritRootScale_sq (m : ℝ) :
    qutritRootScale m ^ 2 = 1 / (4 * qutritNormalization m) := by
  unfold qutritRootScale
  rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt (qutritNormalization_pos m))]
  norm_num

theorem qutritRoot_hermitian (m : ℝ) : (qutritRoot m).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qutritRoot, IsHermitian, conjTranspose_apply]

theorem qutritRoot_posDef {m : ℝ} (hm : 4 ≤ m) : (qutritRoot m).PosDef := by
  refine ⟨qutritRoot_hermitian m, ?_⟩
  intro x hx
  have hp := coordinates_sq_pos x hx
  have hc : 0 ≤ (2 * m - 1) * x 0 ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _)
    linarith
  have hbase : 0 < 2 * m * x 0 ^ 2 + 3 * x 1 ^ 2 +
      2 * x 1 * x 2 + 3 * x 2 ^ 2 := by
    nlinarith [sq_nonneg (x 1 + x 2), sq_nonneg (x 1), sq_nonneg (x 2)]
  have hmul := mul_pos (qutritRootScale_pos m) hbase
  norm_num [dotProduct, mulVec, qutritRoot, Fin.sum_univ_succ]
  nlinarith

theorem qutritRoot_square (m : ℝ) : qutritRoot m * qutritRoot m = qutritState m := by
  have hs := qutritRootScale_sq m
  have hn := qutritNormalization_pos m
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qutritRoot, qutritState, qutritRaw, mul_apply, Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals rw [hs]
  all_goals ring

theorem qutritRoot_is_positive_square_root {m : ℝ} (hm : 4 ≤ m) :
    qutritRoot m = (qutritState_posDef hm).posSemidef.sqrt := by
  exact (qutritRoot_posDef hm).posSemidef.eq_sqrt_of_sq_eq
    (qutritState_posDef hm).posSemidef (by simpa only [pow_two] using qutritRoot_square m)

theorem qutritState_purity (m : ℝ) :
    trace (qutritState m * qutritState m) =
      (m ^ 4 + 17) / (m ^ 2 + 5) ^ 2 := by
  have hn : m ^ 2 + 5 ≠ 0 := ne_of_gt (qutritNormalization_pos m)
  norm_num [trace, qutritState, qutritRaw, mul_apply, qutritNormalization, Fin.sum_univ_succ]
  field_simp
  ring

theorem qutritRoot_normalized (m : ℝ) : States.hsNormSq (qutritRoot m) = 1 := by
  rw [States.hsNormSq_eq_trace]
  have ht : (qutritRoot m)ᵀ = qutritRoot m := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [qutritRoot]
  rw [ht, qutritRoot_square, qutritState_trace]

/-- The two nonzero gap weights each equal half the total nonzero-gap mass. -/
theorem qutritRoot_gap_weights (m : ℝ) : ∀ i : Fin 3,
    States.operatorGapWeight qutritEnergy (qutritRoot m) (threeNodes i) =
      (![qutritWeightS (m ^ 2) / 2, 1 - qutritWeightS (m ^ 2),
        qutritWeightS (m ^ 2) / 2] : Fin 3 → ℝ) i := by
  have hs := qutritRootScale_sq m
  have hn : m ^ 2 + 5 ≠ 0 := ne_of_gt (qutritNormalization_pos m)
  intro i
  fin_cases i <;>
    norm_num [States.operatorGapWeight, States.gapWeight, qutritEnergy,
      qutritRoot, threeNodes, qutritWeightS, Fin.sum_univ_succ]
  all_goals
    unfold qutritNormalization at hs
    field_simp at hs ⊢
    nlinarith

/-- Purity-normalized mixed-state commutator spectral weights. -/
theorem qutritState_gap_weights (m : ℝ) : ∀ i : Fin 3,
    States.operatorGapWeight qutritEnergy (qutritState m) (threeNodes i) /
      trace (qutritState m * qutritState m) =
      (![qutritWeightK (m ^ 2) / 2, 1 - qutritWeightK (m ^ 2),
        qutritWeightK (m ^ 2) / 2] : Fin 3 → ℝ) i := by
  have hn : m ^ 2 + 5 ≠ 0 := ne_of_gt (qutritNormalization_pos m)
  have ht : m ^ 4 + 17 ≠ 0 := by positivity
  intro i
  fin_cases i <;>
    norm_num [States.operatorGapWeight, States.gapWeight, qutritEnergy,
      qutritState, qutritRaw, qutritNormalization, threeNodes, qutritWeightK,
      qutritState_purity, Fin.sum_univ_succ] <;>
    field_simp <;> ring

theorem qutritRoot_gap_support (m ω : ℝ)
    (hm : ω ≠ -1) (h0 : ω ≠ 0) (hp : ω ≠ 1) :
    States.operatorGapWeight qutritEnergy (qutritRoot m) ω = 0 := by
  simp [States.operatorGapWeight, States.gapWeight, qutritEnergy,
    qutritRoot, Fin.sum_univ_succ, Ne.symm hm, Ne.symm h0, Ne.symm hp]

theorem qutritState_gap_support (m ω : ℝ)
    (hm : ω ≠ -1) (h0 : ω ≠ 0) (hp : ω ≠ 1) :
    States.operatorGapWeight qutritEnergy (qutritState m) ω = 0 := by
  simp [States.operatorGapWeight, States.gapWeight, qutritEnergy,
    qutritState, qutritRaw, Fin.sum_univ_succ, Ne.symm hm, Ne.symm h0, Ne.symm hp]

/-! The four-dimensional fixed-purity family. -/

abbrev FourLevel := Matrix (Fin 4) (Fin 4) ℝ

def fixedState (ε : ℝ) : FourLevel :=
  !![fixedPurityEigenPlus ε,0,0,0;
     0,fixedPurityEigenMinus ε,0,0;
     0,0,ε/2,3*ε/10;
     0,0,3*ε/10,ε/2]

def fixedRootScale (ε : ℝ) : ℝ := Real.sqrt (ε / 20)

def fixedRoot (ε : ℝ) : FourLevel :=
  !![Real.sqrt (fixedPurityEigenPlus ε),0,0,0;
     0,Real.sqrt (fixedPurityEigenMinus ε),0,0;
     0,0,3 * fixedRootScale ε,fixedRootScale ε;
     0,0,fixedRootScale ε,3 * fixedRootScale ε]

def fixedEnergy : Fin 4 → ℝ := ![2,3,0,1]

theorem fixedState_hermitian (ε : ℝ) : (fixedState ε).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fixedState, IsHermitian, conjTranspose_apply]

theorem fixedState_trace (ε : ℝ) : trace (fixedState ε) = 1 := by
  norm_num [trace, fixedState, Fin.sum_univ_succ, fixedPurityEigenPlus, fixedPurityEigenMinus]
  ring

theorem fixedState_posDef {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    (fixedState ε).PosDef := by
  have hc := fixedPurity_eigenvalue_certificate he he'
  have ha := hc.2.1
  have hb := hc.2.2.1
  have hd : (diagonal (![fixedPurityEigenPlus ε, fixedPurityEigenMinus ε,
      ε / 5, ε / 5] : Fin 4 → ℝ)).PosDef := by
    apply PosDef.diagonal
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · change 0 < ε / 5
      positivity
    · change 0 < ε / 5
      positivity
  refine ⟨fixedState_hermitian ε, ?_⟩
  intro x hx
  have hp := hd.2 x hx
  have hs : 0 ≤ (3 * ε / 10) * (x 2 + x (Fin.succ 2)) ^ 2 := by positivity
  norm_num [dotProduct, mulVec, fixedState, diagonal, Fin.sum_univ_succ] at hp ⊢
  nlinarith

theorem fixedState_full_rank {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    IsUnit (fixedState ε) := (fixedState_posDef he he').isUnit

theorem fixedState_purity {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    trace (fixedState ε * fixedState ε) = 1 / 2 := by
  have hc := (fixedPurity_eigenvalue_certificate he he').2.2.2.2.2.2
  norm_num [trace, fixedState, mul_apply, Fin.sum_univ_succ]
  nlinarith

theorem fixedRootScale_pos {ε : ℝ} (he : 0 < ε) : 0 < fixedRootScale ε := by
  unfold fixedRootScale
  positivity

theorem fixedRootScale_sq {ε : ℝ} (he : 0 < ε) : fixedRootScale ε ^ 2 = ε / 20 := by
  exact Real.sq_sqrt (by positivity)

theorem fixedRoot_hermitian (ε : ℝ) : (fixedRoot ε).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fixedRoot, IsHermitian, conjTranspose_apply]

theorem fixedRoot_posDef {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    (fixedRoot ε).PosDef := by
  have hc := fixedPurity_eigenvalue_certificate he he'
  have ha := hc.2.1
  have hb := hc.2.2.1
  have hk := fixedRootScale_pos he
  have hd : (diagonal (![Real.sqrt (fixedPurityEigenPlus ε),
      Real.sqrt (fixedPurityEigenMinus ε), 2 * fixedRootScale ε,
      2 * fixedRootScale ε] : Fin 4 → ℝ)).PosDef := by
    apply PosDef.diagonal
    intro i
    fin_cases i
    · exact Real.sqrt_pos.2 ha
    · exact Real.sqrt_pos.2 hb
    · change 0 < 2 * fixedRootScale ε
      positivity
    · change 0 < 2 * fixedRootScale ε
      positivity
  refine ⟨fixedRoot_hermitian ε, ?_⟩
  intro x hx
  have hp := hd.2 x hx
  have hs : 0 ≤ fixedRootScale ε * (x 2 + x (Fin.succ 2)) ^ 2 := by positivity
  norm_num [dotProduct, mulVec, fixedRoot, diagonal, Fin.sum_univ_succ] at hp ⊢
  nlinarith

theorem fixedRoot_square {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    fixedRoot ε * fixedRoot ε = fixedState ε := by
  have hc := fixedPurity_eigenvalue_certificate he he'
  have ha := Real.sq_sqrt (le_of_lt hc.2.1)
  have hb := Real.sq_sqrt (le_of_lt hc.2.2.1)
  have hk := fixedRootScale_sq he
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fixedRoot, fixedState, mul_apply, Fin.sum_univ_succ] <;>
    nlinarith

theorem fixedRoot_is_positive_square_root {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    fixedRoot ε = (fixedState_posDef he he').posSemidef.sqrt := by
  exact (fixedRoot_posDef he he').posSemidef.eq_sqrt_of_sq_eq
    (fixedState_posDef he he').posSemidef (by simpa only [pow_two] using fixedRoot_square he he')

theorem fixedRoot_normalized {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    States.hsNormSq (fixedRoot ε) = 1 := by
  rw [States.hsNormSq_eq_trace]
  have ht : (fixedRoot ε)ᵀ = fixedRoot ε := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fixedRoot]
  rw [ht, fixedRoot_square he he', fixedState_trace]

/-- Exact spectral weights of the canonical square-root seed. -/
theorem fixedRoot_gap_weights {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    ∀ i : Fin 3, States.operatorGapWeight fixedEnergy (fixedRoot ε) (threeNodes i) =
      (![ε / 20, 1 - ε / 10, ε / 20] : Fin 3 → ℝ) i := by
  have hc := fixedPurity_eigenvalue_certificate he he'
  have ha := Real.sq_sqrt (le_of_lt hc.2.1)
  have hb := Real.sq_sqrt (le_of_lt hc.2.2.1)
  have hk := fixedRootScale_sq he
  have hsum := hc.2.2.2.2.2.1
  intro i
  fin_cases i <;>
    norm_num [States.operatorGapWeight, States.gapWeight, fixedEnergy,
      fixedRoot, threeNodes, Fin.sum_univ_succ] <;> nlinarith

/-- Exact purity-normalized spectral weights of the density-matrix seed. -/
theorem fixedState_gap_weights {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    ∀ i : Fin 3, States.operatorGapWeight fixedEnergy (fixedState ε) (threeNodes i) /
      trace (fixedState ε * fixedState ε) =
      (![9 * ε ^ 2 / 50, 1 - 9 * ε ^ 2 / 25, 9 * ε ^ 2 / 50] : Fin 3 → ℝ) i := by
  have hc := (fixedPurity_eigenvalue_certificate he he').2.2.2.2.2.2
  intro i
  rw [fixedState_purity he he']
  fin_cases i <;>
    norm_num [States.operatorGapWeight, States.gapWeight, fixedEnergy,
      fixedState, threeNodes, fixedState_purity he he', Fin.sum_univ_succ] <;> nlinarith

theorem fixedRoot_gap_support (ε ω : ℝ)
    (hm : ω ≠ -1) (h0 : ω ≠ 0) (hp : ω ≠ 1) :
    States.operatorGapWeight fixedEnergy (fixedRoot ε) ω = 0 := by
  simp [States.operatorGapWeight, States.gapWeight, fixedEnergy,
    fixedRoot, Fin.sum_univ_succ, Ne.symm hm, Ne.symm h0, Ne.symm hp]

theorem fixedState_gap_support (ε ω : ℝ)
    (hm : ω ≠ -1) (h0 : ω ≠ 0) (hp : ω ≠ 1) :
    States.operatorGapWeight fixedEnergy (fixedState ε) ω = 0 := by
  simp [States.operatorGapWeight, States.gapWeight, fixedEnergy,
    fixedState, Fin.sum_univ_succ, Ne.symm hm, Ne.symm h0, Ne.symm hp]

theorem qutritHamiltonian_hermitian : (diagonal qutritEnergy).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qutritEnergy, diagonal, IsHermitian, conjTranspose_apply]

theorem fixedHamiltonian_hermitian : (diagonal fixedEnergy).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fixedEnergy, diagonal, IsHermitian, conjTranspose_apply]

theorem qutrit_root_total_weight (m : ℝ) :
    2 * States.operatorGapWeight qutritEnergy (qutritRoot m) 1 =
      qutritWeightS (m ^ 2) := by
  have h := qutritRoot_gap_weights m (2 : Fin 3)
  change States.operatorGapWeight qutritEnergy (qutritRoot m) 1 = qutritWeightS (m ^ 2) / 2 at h
  linarith

theorem qutrit_state_total_weight (m : ℝ) :
    2 * (States.operatorGapWeight qutritEnergy (qutritState m) 1 /
      trace (qutritState m * qutritState m)) = qutritWeightK (m ^ 2) := by
  have h := qutritState_gap_weights m (2 : Fin 3)
  change States.operatorGapWeight qutritEnergy (qutritState m) 1 / trace (qutritState m * qutritState m) = qutritWeightK (m ^ 2) / 2 at h
  linarith

theorem fixed_root_total_weight {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    2 * States.operatorGapWeight fixedEnergy (fixedRoot ε) 1 = ε / 10 := by
  have h := fixedRoot_gap_weights he he' (2 : Fin 3)
  change States.operatorGapWeight fixedEnergy (fixedRoot ε) 1 = ε / 20 at h
  linarith

theorem fixed_state_total_weight {ε : ℝ} (he : 0 < ε) (he' : ε < 5 / 18) :
    2 * (States.operatorGapWeight fixedEnergy (fixedState ε) 1 /
      trace (fixedState ε * fixedState ε)) = 9 * ε ^ 2 / 25 := by
  have h := fixedState_gap_weights he he' (2 : Fin 3)
  change States.operatorGapWeight fixedEnergy (fixedState ε) 1 / trace (fixedState ε * fixedState ε) = 9 * ε ^ 2 / 50 at h
  linarith

/-- The fixed-purity ratio expressed directly in spectral weights of the
actual positive density matrix and its canonical positive square root. -/
theorem fixed_matrix_weight_quotient {ε x : ℝ} (he : 0 < ε) (he' : ε < 5 / 18)
    (hx : 0 < x) :
    threeAtomComplexity (2 * States.operatorGapWeight fixedEnergy (fixedRoot ε) 1) x /
      threeAtomComplexity (2 * (States.operatorGapWeight fixedEnergy (fixedState ε) 1 /
        trace (fixedState ε * fixedState ε))) x = fixedPurityRatio ε x := by
  rw [fixed_root_total_weight he he', fixed_state_total_weight he he']
  exact fixedPurity_spectral_quotient he he' hx

/-- Matrix-weight form of the no-positive-multiplier theorem. This uses the
three-atom complexity formula on the directly computed physical gap weights. -/
theorem qutrit_matrix_weights_no_positive_multiplier :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, 4 ≤ m →
      c * threeAtomComplexity
        (2 * States.operatorGapWeight qutritEnergy (qutritRoot m) 1) 1 ≤
      threeAtomComplexity (2 * (States.operatorGapWeight qutritEnergy (qutritState m) 1 /
        trace (qutritState m * qutritState m))) 1 := by
  simpa only [qutrit_root_total_weight, qutrit_state_total_weight] using
    qutrit_no_positive_multiplier

/-- Uniform unboundedness with admissibility and fixed purity of each finite
matrix witness included in the existential conclusion. -/
theorem fixed_matrix_weights_uniform_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 5 / 18 ∧ (fixedState ε).PosDef ∧
      trace (fixedState ε) = 1 ∧ trace (fixedState ε * fixedState ε) = 1 / 2 ∧
      ∀ x : ℝ, 0 < x → x ≤ 1 →
        M < threeAtomComplexity (2 * States.operatorGapWeight fixedEnergy (fixedRoot ε) 1) x /
          threeAtomComplexity (2 * (States.operatorGapWeight fixedEnergy (fixedState ε) 1 /
            trace (fixedState ε * fixedState ε))) x := by
  obtain ⟨ε, he, he', h⟩ := fixedPurity_uniform_unbounded M
  refine ⟨ε, he, he', fixedState_posDef he he', fixedState_trace ε,
    fixedState_purity he he', ?_⟩
  intro x hx hx'
  rw [fixed_matrix_weight_quotient he he' hx]
  exact h x (le_of_lt hx) hx'

/-- Exact bridge between the time-domain three-atom formula and the scalar
polynomial used in `Ratios`. -/
theorem threeAtom_time_eq (μ t : ℝ) :
    Qubit.threeAtom μ t = threeAtomComplexity μ (Real.sin (t / 2) ^ 2) :=
  Qubit.threeAtom_polynomial μ t

/-- The fixed-purity scalar ratio is the quotient of actual three-site Jacobi
matrix-exponential complexities with the physical matrix family's gap weights. -/
theorem fixed_jacobi_quotient {ε t : ℝ} (he : 0 < ε) (he' : ε < 5 / 18)
    (ht : Real.sin (t / 2) ≠ 0) :
    Qubit.matrixChainComplexity (ε / 10) t /
      Qubit.matrixChainComplexity (9 * ε ^ 2 / 25) t =
        fixedPurityRatio ε (Real.sin (t / 2) ^ 2) := by
  have hS : ε / 10 ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
  have hK : 9 * ε ^ 2 / 25 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · have hp := mul_pos he (sub_pos.mpr he')
      nlinarith
  rw [Qubit.matrixChainComplexity_eq hS, Qubit.matrixChainComplexity_eq hK,
    threeAtom_time_eq, threeAtom_time_eq]
  exact fixedPurity_spectral_quotient he he' (sq_pos_of_ne_zero ht)

/-- Uniform divergence for the actual reduced Jacobi evolutions, with each
finite density-matrix witness certified positive, normalized and purity `1/2`. -/
theorem fixed_jacobi_uniform_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 5 / 18 ∧ (fixedState ε).PosDef ∧
      trace (fixedState ε) = 1 ∧ trace (fixedState ε * fixedState ε) = 1 / 2 ∧
      ∀ t : ℝ, Real.sin (t / 2) ≠ 0 →
        M < Qubit.matrixChainComplexity (ε / 10) t /
          Qubit.matrixChainComplexity (9 * ε ^ 2 / 25) t := by
  obtain ⟨ε, he, he', h⟩ := fixedPurity_uniform_unbounded M
  refine ⟨ε, he, he', fixedState_posDef he he', fixedState_trace ε,
    fixedState_purity he he', ?_⟩
  intro t ht
  rw [fixed_jacobi_quotient he he' ht]
  exact h _ (sq_nonneg _) (Real.sin_sq_le_one _)

/-- The unbounded qutrit ratio theorem also holds for the actual Jacobi
matrix exponentials, rather than only for an algebraically defined complexity. -/
theorem qutrit_jacobi_no_positive_multiplier :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, 4 ≤ m →
      c * Qubit.matrixChainComplexity (qutritWeightS (m ^ 2)) Real.pi ≤
        Qubit.matrixChainComplexity (qutritWeightK (m ^ 2)) Real.pi := by
  rintro ⟨c, hc, hall⟩
  apply qutrit_no_positive_multiplier
  refine ⟨c, hc, ?_⟩
  intro m hm
  have hz : 16 ≤ m ^ 2 := by nlinarith
  have hw := qutrit_weights hz
  have hS : qutritWeightS (m ^ 2) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hw.1, hw.2.1, hw.2.2.2]
  have hK : qutritWeightK (m ^ 2) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hw.1, hw.2.1, hw.2.2.2]
  have h := hall m hm
  rw [Qubit.matrixChainComplexity_eq hS, Qubit.matrixChainComplexity_eq hK,
    threeAtom_time_eq, threeAtom_time_eq] at h
  simpa only [Real.sin_pi_div_two, one_pow] using h

end Krylov.FamilyStates
