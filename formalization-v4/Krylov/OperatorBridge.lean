import Krylov.States
import Krylov.Spectral

/-!
An operator-level bridge for diagonal Hamiltonians.  The Liouvillian is a
complex-linear endomorphism and is proved equal to the actual matrix
commutator. Polynomial functional calculus, Hilbert--Schmidt inner products,
finite spectral grouping and diagonal-unitary time evolution are proved
entrywise; no claimed physical complexity is defined by fiat.
-/
namespace Krylov.OperatorBridge
open Matrix
open scoped BigOperators
noncomputable section

abbrev Operator (ι : Type*) := Matrix ι ι ℂ

def hamiltonian {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) : Operator ι :=
  diagonal (fun i => (E i : ℂ))

def liouvillian {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) : Module.End ℂ (Operator ι) where
  toFun A := fun i j => ((E i - E j : ℝ) : ℂ) * A i j
  map_add' A B := by ext i j; simp [mul_add]
  map_smul' c A := by ext i j; simp [mul_left_comm]

theorem liouvillian_commutator {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (A : Operator ι) :
    liouvillian E A = hamiltonian E * A - A * hamiltonian E := by
  ext i j
  simp [liouvillian, hamiltonian, sub_mul]; ring

theorem liouvillian_pow_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (k : ℕ)
    (A : Operator ι) (i j : ι) :
    (((liouvillian E)^k) A) i j = (((E i - E j : ℝ) : ℂ))^k * A i j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (((E i - E j : ℝ) : ℂ)) * (((liouvillian E)^k) A) i j = _
    rw [ih, pow_succ']; ring

/-- The entrywise spectral multiplier really is the polynomial in the commutator. -/
theorem polynomial_liouvillian_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ)
    (p : Polynomial ℂ) (A : Operator ι) (i j : ι) :
    ((Polynomial.aeval (liouvillian E)) p A) i j =
      p.eval (((E i - E j : ℝ) : ℂ)) * A i j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq, add_mul]
  | monomial k a =>
    simp [Polynomial.aeval_monomial, Module.End.mul_apply,
      liouvillian_pow_entry, Polynomial.eval_monomial, mul_assoc]

def hsInner {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Operator ι) : ℂ :=
  ∑ i, ∑ j, star (A i j) * B i j

def spectralFilter {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (f : ℝ → ℂ) (A : Operator ι) : Operator ι :=
  fun i j => f (E i - E j) * A i j

theorem polynomial_eq_spectralFilter {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ)
    (p : Polynomial ℂ) (A : Operator ι) :
    (Polynomial.aeval (liouvillian E)) p A =
      spectralFilter E (fun x => p.eval (x : ℂ)) A := by
  ext i j; exact polynomial_liouvillian_entry E p A i j

def gapWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (A : Operator ι) (ω : ℝ) : ℝ :=
  ∑ i, ∑ j, if E i - E j = ω then Complex.normSq (A i j) else 0

theorem hsInner_filters_entries {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (f g : ℝ → ℂ)
    (A : Operator ι) :
    hsInner (spectralFilter E f A) (spectralFilter E g A) =
      ∑ i, ∑ j, (Complex.normSq (A i j) : ℂ) *
        star (f (E i - E j)) * g (E i - E j) := by
  unfold hsInner spectralFilter
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def, map_mul]
  ring

/-- Grouping entry weights by a finite set of energy gaps. -/
theorem group_gap_weights {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (A : Operator ι)
    (f : ℝ → ℂ) (S : Finset ℝ) (hS : ∀ i j, E i - E j ∈ S) :
    (∑ ω ∈ S, (gapWeight E A ω : ℂ) * f ω) =
      ∑ i, ∑ j, (Complex.normSq (A i j) : ℂ) * f (E i - E j) := by
  classical
  simp only [gapWeight, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [hS]

/-- Zero entries need not contribute their gap to the chosen support. -/
theorem group_gap_weights_supported {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (A : Operator ι)
    (f : ℝ → ℂ) (S : Finset ℝ)
    (hS : ∀ i j, A i j ≠ 0 → E i - E j ∈ S) :
    (∑ ω ∈ S, (gapWeight E A ω : ℂ) * f ω) =
      ∑ i, ∑ j, (Complex.normSq (A i j) : ℂ) * f (E i - E j) := by
  classical
  simp only [gapWeight, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  by_cases hm : E i - E j ∈ S
  · simp [hm]
  · have hz : A i j = 0 := by
      by_contra hn; exact hm (hS i j hn)
    simp [hm, hz]

theorem hsInner_filters_grouped {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (f g : ℝ → ℂ)
    (A : Operator ι) (S : Finset ℝ) (hS : ∀ i j, E i - E j ∈ S) :
    hsInner (spectralFilter E f A) (spectralFilter E g A) =
      ∑ ω ∈ S, (gapWeight E A ω : ℂ) * star (f ω) * g ω := by
  rw [hsInner_filters_entries]
  simpa only [mul_assoc] using
    (group_gap_weights E A (fun ω => star (f ω) * g ω) S hS).symm

theorem hsInner_polynomials_grouped {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (p q : Polynomial ℂ)
    (A : Operator ι) (S : Finset ℝ) (hS : ∀ i j, E i - E j ∈ S) :
    hsInner ((Polynomial.aeval (liouvillian E)) p A)
      ((Polynomial.aeval (liouvillian E)) q A) =
        ∑ ω ∈ S, (gapWeight E A ω : ℂ) * star (p.eval (ω : ℂ)) * q.eval (ω : ℂ) := by
  rw [polynomial_eq_spectralFilter, polynomial_eq_spectralFilter]
  exact hsInner_filters_grouped E _ _ A S hS

theorem hsInner_filters_supported {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (f g : ℝ → ℂ)
    (A : Operator ι) (S : Finset ℝ)
    (hS : ∀ i j, A i j ≠ 0 → E i - E j ∈ S) :
    hsInner (spectralFilter E f A) (spectralFilter E g A) =
      ∑ ω ∈ S, (gapWeight E A ω : ℂ) * star (f ω) * g ω := by
  rw [hsInner_filters_entries]
  simpa only [mul_assoc] using
    (group_gap_weights_supported E A (fun ω => star (f ω) * g ω) S hS).symm

/-- The real matrices in the state certificates have exactly these complex weights. -/
theorem real_gapWeight {n : ℕ} (E : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    gapWeight E (A.map Complex.ofReal) ω = States.operatorGapWeight E A ω := by
  simp [gapWeight, States.operatorGapWeight, States.gapWeight, Complex.normSq_ofReal, pow_two]

/-! Exact named links to the weights used by the kernel-checked spectral certificates. -/
theorem right_mixed_weights_certified : ∀ i : Fin 3,
    gapWeight States.energyR (States.rhoRE.map Complex.ofReal)
      (Spectral.RightMixed.nodes i : ℝ) / Matrix.trace (States.rhoR * States.rhoR) =
        (Spectral.RightMixed.weights i : ℝ) := by
  intro i
  rw [real_gapWeight]
  have h := States.right_mixed_gap_weights i
  fin_cases i <;> norm_num [Spectral.RightMixed.nodes, Spectral.RightMixed.weights,
    States.rightMixedNodes] at * <;> assumption

theorem left_mixed_weights_certified : ∀ i : Fin 3,
    gapWeight States.energyL (States.rhoL.map Complex.ofReal)
      (Spectral.LeftMixed.nodes i : ℝ) / Matrix.trace (States.rhoL * States.rhoL) =
        (Spectral.LeftMixed.weights i : ℝ) := by
  intro i
  rw [real_gapWeight]
  have h := States.left_mixed_gap_weights i
  fin_cases i <;> norm_num [Spectral.LeftMixed.nodes, Spectral.LeftMixed.weights,
    States.leftNodes] at * <;> assumption

theorem left_spread_weights_certified : ∀ i : Fin 3,
    gapWeight States.energyL (States.rootL.map Complex.ofReal)
      (Spectral.LeftSpread.nodes i : ℝ) = (Spectral.LeftSpread.weights i : ℝ) := by
  intro i
  rw [real_gapWeight]
  have h := States.left_spread_gap_weights i
  fin_cases i <;> norm_num [Spectral.LeftSpread.nodes, Spectral.LeftSpread.weights,
    States.leftNodes] at * <;> assumption

theorem right_purified_weights_certified : ∀ i : Fin 5,
    States.pureGapWeight States.energyR (fun a => States.rhoRE a a)
      (Spectral.RightPurified.nodes i : ℝ) = (Spectral.RightPurified.weights i : ℝ) := by
  intro i
  have h := States.right_purified_gap_weights i
  fin_cases i <;> norm_num [Spectral.RightPurified.nodes, Spectral.RightPurified.weights,
    States.rightPurifiedNodes] at * <;> assumption

def phase (ω t : ℝ) : ℂ := Complex.exp (((-(ω*t) : ℝ) : ℂ) * Complex.I)

def diagonalUnitary {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (t : ℝ) : Operator ι :=
  diagonal (fun i => phase (E i) t)

/-- The diagonal phase matrix is the actual power-series matrix exponential. -/
theorem diagonalUnitary_eq_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (t : ℝ) :
    diagonalUnitary E t = NormedSpace.exp ℂ ((((-t : ℝ) : ℂ) * Complex.I) • hamiltonian E) := by
  unfold diagonalUnitary hamiltonian
  rw [← diagonal_smul, Matrix.exp_diagonal]
  apply congrArg diagonal
  funext i
  simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  unfold phase
  congr 1; push_cast; ring

theorem phase_conj (ω t : ℝ) : star (phase ω t) = phase (-ω) t := by
  simp [phase, Complex.star_def, ← Complex.exp_conj]

theorem phase_difference (a b t : ℝ) :
    phase a t * star (phase b t) = phase (a-b) t := by
  rw [phase_conj]
  unfold phase
  rw [← Complex.exp_add]
  congr 1; push_cast; ring

theorem diagonalUnitary_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (t : ℝ)
    (A : Operator ι) :
    diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ =
      spectralFilter E (fun ω => phase ω t) A := by
  ext i j
  simp only [diagonalUnitary, diagonal_conjTranspose, diagonal_mul, mul_diagonal,
    spectralFilter, Pi.star_apply]
  rw [mul_right_comm, phase_difference]

theorem hsInner_polynomial_evolved {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ) (p : Polynomial ℂ)
    (A : Operator ι) (t : ℝ) (S : Finset ℝ) (hS : ∀ i j, E i - E j ∈ S) :
    hsInner ((Polynomial.aeval (liouvillian E)) p A)
      (diagonalUnitary E t * A * (diagonalUnitary E t)ᴴ) =
        ∑ ω ∈ S, (gapWeight E A ω : ℂ) * star (p.eval (ω : ℂ)) * phase ω t := by
  rw [polynomial_eq_spectralFilter, diagonalUnitary_conjugation]
  exact hsInner_filters_grouped E _ _ A S hS

end
end Krylov.OperatorBridge
