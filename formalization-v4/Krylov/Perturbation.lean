import Krylov.States
import Krylov.ShortTime

/-! Algebraic physical certificates for the irreducible perturbed qutrit.
The dynamical Taylor-remainder bridge is separate from the exact curvature
and common-reducing-projection statements below. -/
namespace Krylov.Perturbation
open Matrix
open scoped BigOperators
noncomputable section

def hamiltonian (δ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0,1,δ;1,0,2*δ;δ,2*δ,0]

theorem hermitian (δ : ℝ) : (hamiltonian δ).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hamiltonian,Matrix.IsHermitian,Matrix.conjTranspose_apply]

def mixedCurvature (δ : ℝ) : ℝ :=
  States.hsNormSq (hamiltonian δ * States.rhoR - States.rhoR * hamiltonian δ) /
    Matrix.trace (States.rhoR * States.rhoR)

def purifiedCurvature (δ : ℝ) : ℝ :=
  2 * (Matrix.trace (States.rhoR * (hamiltonian δ * hamiltonian δ)) -
    Matrix.trace (States.rhoR * hamiltonian δ)^2)

theorem curvature_gap (δ : ℝ) :
    mixedCurvature δ - purifiedCurvature δ = (4-540*δ^2)/169 := by
  have hr : States.rhoR = !![8/13,0,0;0,1/26,0;0,0,9/26] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [States.rhoR,Matrix.diagonal]
  norm_num [mixedCurvature,purifiedCurvature,States.hsNormSq,Matrix.trace,
    Matrix.mul_apply,hr,hamiltonian,Fin.sum_univ_succ]
  ring

theorem curvature_gap_positive {δ : ℝ} (h : δ^2 < 1/135) :
    purifiedCurvature δ < mixedCurvature δ := by
  have hp := ShortTime.perturbed_quadratic_gap h
  rw [← curvature_gap] at hp
  linarith

theorem curvature_finite : mixedCurvature (1/20) - purifiedCurvature (1/20) = 53/3380 := by
  rw [curvature_gap]; norm_num

/-- Commuting with the simple-spectrum displayed density forces diagonality. -/
theorem commuting_density_diagonal (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hP : P * States.rhoR.map Complex.ofReal = States.rhoR.map Complex.ofReal * P) :
    P = Matrix.diagonal (fun i => P i i) := by
  let d : Fin 3 → ℂ := ![8/13,1/26,9/26]
  have hr : States.rhoR.map Complex.ofReal = Matrix.diagonal d := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [States.rhoR,d,Matrix.diagonal]
  rw [hr] at hP
  ext i j
  by_cases hij : i=j
  · subst j; simp
  · have h := congrFun (congrFun hP i) j
    simp only [Matrix.mul_diagonal,Matrix.diagonal_mul] at h
    have hz : (d j-d i)*P i j=0 := by linear_combination h
    have hne : d j-d i ≠ 0 := by
      fin_cases i <;> fin_cases j <;> norm_num [d] at *
    have hp : P i j=0 := (mul_eq_zero.mp hz).resolve_left hne
    simp [Matrix.diagonal,hij,hp]


/-- Stronger than absence of a common reducing projection: every idempotent
commuting with both rho and H is zero or the identity, even without imposing
self-adjointness of the idempotent. -/
theorem no_common_nontrivial_idempotent {δ : ℝ} (hδ : δ ≠ 0)
    (P : Matrix (Fin 3) (Fin 3) ℂ) (hId : P*P=P)
    (hρ : P * States.rhoR.map Complex.ofReal = States.rhoR.map Complex.ofReal * P)
    (hH : P * (hamiltonian δ).map Complex.ofReal = (hamiltonian δ).map Complex.ofReal * P) :
    P=0 ∨ P=1 := by
  have hd := commuting_density_diagonal P hρ
  have h01 := congrFun (congrFun hH 0) 1
  have h02 := congrFun (congrFun hH 0) 2
  rw [hd] at h01 h02
  norm_num [hamiltonian,Matrix.diagonal_mul,Matrix.mul_diagonal] at h01 h02
  have hz : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ
  have he : P 0 0 = P 2 2 := by
    apply (mul_right_cancel₀ hz)
    simpa [mul_comm] using h02
  have hi := congrFun (congrFun hId 0) 0
  rw [hd] at hi
  simp only [Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply_eq] at hi
  have hroot : P 0 0=0 ∨ P 0 0=1 := by
    have hfactor : P 0 0*(P 0 0-1)=0 := by linear_combination hi
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hroot with hz0 | hz1
  · left; rw [hd]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal,hz0,←h01,←he]
  · right; rw [hd]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal,hz1,←h01,←he]

end
end Krylov.Perturbation
