import Krylov.States
import Krylov.TemporalFamilies

/-!
# Physical certificates for the two temporal-ratio families

The statements below concern actual four-dimensional real symmetric matrices:
positivity, normalization, canonical positive roots, purity, and the spectral
weights of the diagonal commutator. They do not assert a general Lanczos/CV
identification or a removable-ratio theorem.
-/
noncomputable section
namespace Krylov.TemporalStates
open Matrix
open scoped BigOperators
open Krylov.TemporalFamilies

abbrev FourLevel := Matrix (Fin 4) (Fin 4) ℝ

def block (a b c d : ℝ) : FourLevel :=
  !![a,b,0,0; b,a,0,0; 0,0,c,d; 0,0,d,c]

def energy : Fin 4 → ℝ := ![0,2,3,4]
def hamiltonian : FourLevel := diagonal energy
def nodes : Fin 5 → ℝ := ![-2,-1,0,1,2]

theorem hamiltonian_hermitian : hamiltonian.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [hamiltonian, energy, IsHermitian, conjTranspose_apply, diagonal]

theorem block_hermitian (a b c d : ℝ) : (block a b c d).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [block, IsHermitian, conjTranspose_apply]

theorem block_square (a b c d : ℝ) :
    block a b c d * block a b c d =
      block (a^2+b^2) (2*a*b) (c^2+d^2) (2*c*d) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [block, mul_apply, Fin.sum_univ_succ] <;> ring

theorem block_posDef {a b c d : ℝ} (hab : 0 < a-b) (hb : 0 ≤ b)
    (hcd : 0 < c-d) (hd : 0 ≤ d) : (block a b c d).PosDef := by
  have hp : (diagonal (![a-b,a-b,c-d,c-d] : Fin 4 → ℝ)).PosDef := by
    apply PosDef.diagonal
    intro i; fin_cases i <;> norm_num <;> linarith
  refine ⟨block_hermitian a b c d, ?_⟩
  intro x hx
  have hbase := hp.2 x hx
  have h1 := mul_nonneg hb (sq_nonneg (x 0 + x 1))
  have h2 := mul_nonneg hd (sq_nonneg (x 2 + x (Fin.succ 2)))
  norm_num [dotProduct, mulVec, block, diagonal, Fin.sum_univ_succ] at hbase ⊢
  nlinarith

theorem block_trace (a b c d : ℝ) : trace (block a b c d) = 2*a+2*c := by
  norm_num [trace, block, Fin.sum_univ_succ]; ring

theorem block_gap_weights (a b c d : ℝ) : ∀ i : Fin 5,
    States.operatorGapWeight energy (block a b c d) (nodes i) =
      (![b^2,d^2,2*a^2+2*c^2,d^2,b^2] : Fin 5 → ℝ) i := by
  intro i; fin_cases i <;>
    norm_num [States.operatorGapWeight, States.gapWeight, energy, nodes,
      block, Fin.sum_univ_succ] <;> ring

theorem block_gap_support (a b c d ω : ℝ) (hm2 : ω ≠ -2) (hm1 : ω ≠ -1)
    (h0 : ω ≠ 0) (hp1 : ω ≠ 1) (hp2 : ω ≠ 2) :
    States.operatorGapWeight energy (block a b c d) ω = 0 := by
  norm_num [States.operatorGapWeight, States.gapWeight, energy, block, Fin.sum_univ_succ,
    Ne.symm hm2, Ne.symm hm1, Ne.symm h0, Ne.symm hp1, Ne.symm hp2]

/-! Main-ratio family. -/
def mainState (ε : ℝ) : FourLevel := block ((1-ε)/2) (3*(1-ε)/10) (ε/2) (3*ε/10)
def mainScale (ε : ℝ) : ℝ := Real.sqrt (ε/20)
def mainRoot (ε : ℝ) : FourLevel :=
  block (3*mainScale (1-ε)) (mainScale (1-ε)) (3*mainScale ε) (mainScale ε)

theorem mainState_hermitian (ε : ℝ) : (mainState ε).IsHermitian := block_hermitian _ _ _ _
theorem mainRoot_hermitian (ε : ℝ) : (mainRoot ε).IsHermitian := block_hermitian _ _ _ _

theorem mainState_trace (ε : ℝ) : trace (mainState ε) = 1 := by
  rw [mainState, block_trace]; ring

theorem mainState_posDef {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    (mainState ε).PosDef := by
  apply block_posDef <;> dsimp <;> linarith

theorem mainState_full_rank {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    IsUnit (mainState ε) := (mainState_posDef he he').isUnit

theorem mainScale_pos {ε : ℝ} (he : 0 < ε) : 0 < mainScale ε := by
  unfold mainScale; positivity

theorem mainScale_sq {ε : ℝ} (he : 0 ≤ ε) : mainScale ε ^ 2 = ε/20 :=
  Real.sq_sqrt (by positivity)

theorem mainRoot_posDef {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    (mainRoot ε).PosDef := by
  have h1 := mainScale_pos (show 0 < 1-ε by linarith)
  have h2 := mainScale_pos he
  apply block_posDef <;> dsimp <;> linarith

theorem mainRoot_square {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    mainRoot ε * mainRoot ε = mainState ε := by
  have h1 := mainScale_sq (show 0 ≤ 1-ε by linarith)
  have h2 := mainScale_sq (le_of_lt he)
  rw [mainRoot, block_square]
  unfold mainState
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [block] <;> nlinarith

theorem mainRoot_is_positive_square_root {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    mainRoot ε = (mainState_posDef he he').posSemidef.sqrt := by
  exact (mainRoot_posDef he he').posSemidef.eq_sqrt_of_sq_eq
    (mainState_posDef he he').posSemidef (by simpa only [pow_two] using mainRoot_square he he')

theorem mainState_purity (ε : ℝ) :
    trace (mainState ε * mainState ε) = 17 * mainD ε / 25 := by
  rw [mainState, block_square, block_trace]; unfold mainD; ring

theorem mainRoot_normalized {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    States.hsNormSq (mainRoot ε) = 1 := by
  rw [States.hsNormSq_eq_trace]
  have ht : (mainRoot ε)ᵀ = mainRoot ε := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mainRoot, block]
  rw [ht, mainRoot_square he he', mainState_trace]

theorem mainRoot_gap_weights {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) : ∀ i : Fin 5,
    States.operatorGapWeight energy (mainRoot ε) (nodes i) =
      (![(1-ε)/20, ε/20, 9/10, ε/20, (1-ε)/20] : Fin 5 → ℝ) i := by
  have h1 := mainScale_sq (show 0 ≤ 1-ε by linarith)
  have h2 := mainScale_sq (le_of_lt he)
  intro i; rw [mainRoot, block_gap_weights]
  fin_cases i <;> norm_num <;> nlinarith

theorem mainState_gap_weights {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) : ∀ i : Fin 5,
    States.operatorGapWeight energy (mainState ε) (nodes i) /
      trace (mainState ε * mainState ε) =
      (![9*(1-ε)^2/(68*mainD ε),9*ε^2/(68*mainD ε),25/34,
        9*ε^2/(68*mainD ε),9*(1-ε)^2/(68*mainD ε)] : Fin 5 → ℝ) i := by
  have hd : mainD ε ≠ 0 := by have h := (mainD_bounds he he').1; linarith
  intro i; rw [mainState_purity, mainState, block_gap_weights]
  fin_cases i <;> norm_num <;> field_simp <;> unfold mainD <;> ring

/-! Reciprocal-ratio family, parameterized by η with ε = η². -/
def reciprocalRaw (η : ℝ) : FourLevel := block (2*η) η 1 (η^3)
def reciprocalState (η : ℝ) : FourLevel :=
  block (5*η^2 / reciprocalN (η^2)) (4*η^2 / reciprocalN (η^2))
    ((1+η^6) / reciprocalN (η^2)) (2*η^3 / reciprocalN (η^2))
def reciprocalScale (η : ℝ) : ℝ := 1 / Real.sqrt (reciprocalN (η^2))
def reciprocalRoot (η : ℝ) : FourLevel :=
  block (2*η*reciprocalScale η) (η*reciprocalScale η)
    (reciprocalScale η) (η^3*reciprocalScale η)

theorem reciprocalN_pos (η : ℝ) : 0 < reciprocalN (η^2) := by
  unfold reciprocalN; positivity

theorem reciprocalT_pos (η : ℝ) : 0 < reciprocalT (η^2) := by
  unfold reciprocalT; positivity

theorem reciprocal_cube_lt_one {η : ℝ} (hη : 0 < η) (hη' : η^2 ≤ 1/16) : η^3 < 1 := by
  have hq : η ≤ 1/4 := by nlinarith
  have hcube := pow_le_pow_left₀ (le_of_lt hη) hq 3
  norm_num at hcube
  linarith

theorem reciprocalRaw_hermitian (η : ℝ) : (reciprocalRaw η).IsHermitian :=
  block_hermitian _ _ _ _
theorem reciprocalState_hermitian (η : ℝ) : (reciprocalState η).IsHermitian :=
  block_hermitian _ _ _ _
theorem reciprocalRoot_hermitian (η : ℝ) : (reciprocalRoot η).IsHermitian :=
  block_hermitian _ _ _ _

theorem reciprocalRaw_posDef {η : ℝ} (hη : 0 < η) (hη' : η^2 ≤ 1/16) :
    (reciprocalRaw η).PosDef := by
  have hc := reciprocal_cube_lt_one hη hη'
  apply block_posDef
  · dsimp; linarith
  · exact le_of_lt hη
  · dsimp; linarith
  · positivity

theorem reciprocalRaw_trace_square (η : ℝ) :
    trace (reciprocalRaw η * reciprocalRaw η) = reciprocalN (η^2) := by
  rw [reciprocalRaw, block_square, block_trace]; unfold reciprocalN; ring

theorem reciprocalState_eq_normalized_square (η : ℝ) :
    reciprocalState η = (1 / reciprocalN (η^2)) • (reciprocalRaw η * reciprocalRaw η) := by
  rw [reciprocalRaw, block_square]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [reciprocalState, block] <;> ring

theorem reciprocalState_trace (η : ℝ) : trace (reciprocalState η) = 1 := by
  have hn : reciprocalN (η^2) ≠ 0 := ne_of_gt (reciprocalN_pos η)
  rw [reciprocalState, block_trace]
  field_simp; unfold reciprocalN; ring

theorem reciprocalState_posDef {η : ℝ} (hη : 0 < η) (hη' : η^2 ≤ 1/16) :
    (reciprocalState η).PosDef := by
  have hn := reciprocalN_pos η
  have hc := reciprocal_cube_lt_one hη hη'
  apply block_posDef
  · change 0 < 5*η^2 / _ - 4*η^2 / _
    rw [← sub_div]; apply div_pos _ hn; nlinarith [sq_pos_of_pos hη]
  · positivity
  · change 0 < (1+η^6) / _ - 2*η^3 / _
    rw [← sub_div]
    apply div_pos _ hn
    have hs := sq_pos_of_pos (show 0 < 1-η^3 by linarith)
    nlinarith
  · positivity

theorem reciprocalState_full_rank {η : ℝ} (hη : 0 < η) (hη' : η^2 ≤ 1/16) :
    IsUnit (reciprocalState η) := (reciprocalState_posDef hη hη').isUnit

theorem reciprocalScale_pos (η : ℝ) : 0 < reciprocalScale η := by
  have hn := reciprocalN_pos η
  unfold reciprocalScale; positivity

theorem reciprocalScale_sq (η : ℝ) :
    reciprocalScale η ^ 2 = 1 / reciprocalN (η^2) := by
  unfold reciprocalScale
  rw [div_pow, Real.sq_sqrt (le_of_lt (reciprocalN_pos η))]; norm_num

theorem reciprocalRoot_posDef {η : ℝ} (hη : 0 < η) (hη' : η^2 ≤ 1/16) :
    (reciprocalRoot η).PosDef := by
  have hs := reciprocalScale_pos η
  have hc := reciprocal_cube_lt_one hη hη'
  apply block_posDef
  · change 0 < 2*η*reciprocalScale η - η*reciprocalScale η
    nlinarith [mul_pos hη hs]
  · positivity
  · change 0 < reciprocalScale η - η^3*reciprocalScale η
    nlinarith [mul_pos (show 0 < 1-η^3 by linarith) hs]
  · positivity

theorem reciprocalRoot_square (η : ℝ) :
    reciprocalRoot η * reciprocalRoot η = reciprocalState η := by
  have hs := reciprocalScale_sq η
  rw [reciprocalRoot, block_square]
  unfold reciprocalState
  ring_nf
  rw [hs]
  ring

theorem reciprocalRoot_is_positive_square_root {η : ℝ} (hη : 0 < η) (hη' : η^2 ≤ 1/16) :
    reciprocalRoot η = (reciprocalState_posDef hη hη').posSemidef.sqrt := by
  exact (reciprocalRoot_posDef hη hη').posSemidef.eq_sqrt_of_sq_eq
    (reciprocalState_posDef hη hη').posSemidef
    (by simpa only [pow_two] using reciprocalRoot_square η)

theorem reciprocalRaw_trace_fourth (η : ℝ) :
    trace ((reciprocalRaw η * reciprocalRaw η) * (reciprocalRaw η * reciprocalRaw η)) =
      reciprocalT (η^2) := by
  rw [reciprocalRaw, block_square, block_square, block_trace]
  unfold reciprocalT; ring

theorem reciprocalState_purity (η : ℝ) :
    trace (reciprocalState η * reciprocalState η) =
      reciprocalT (η^2) / reciprocalN (η^2)^2 := by
  have hn : reciprocalN (η^2) ≠ 0 := ne_of_gt (reciprocalN_pos η)
  rw [reciprocalState, block_square, block_trace]
  field_simp; unfold reciprocalT; ring

theorem reciprocalRoot_normalized (η : ℝ) : States.hsNormSq (reciprocalRoot η) = 1 := by
  rw [States.hsNormSq_eq_trace]
  have ht : (reciprocalRoot η)ᵀ = reciprocalRoot η := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [reciprocalRoot, block]
  rw [ht, reciprocalRoot_square, reciprocalState_trace]

theorem reciprocalRoot_gap_weights (η : ℝ) : ∀ i : Fin 5,
    States.operatorGapWeight energy (reciprocalRoot η) (nodes i) =
      (![η^2/reciprocalN (η^2),η^6/reciprocalN (η^2),
        (2+8*η^2)/reciprocalN (η^2),η^6/reciprocalN (η^2),
        η^2/reciprocalN (η^2)] : Fin 5 → ℝ) i := by
  have hs := reciprocalScale_sq η
  intro i; rw [reciprocalRoot, block_gap_weights]
  fin_cases i <;> norm_num <;> ring_nf <;> rw [hs] <;> ring

theorem reciprocalState_gap_weights (η : ℝ) : ∀ i : Fin 5,
    States.operatorGapWeight energy (reciprocalState η) (nodes i) /
      trace (reciprocalState η * reciprocalState η) =
      (![16*η^4/reciprocalT (η^2),4*η^6/reciprocalT (η^2),
        (2+50*η^4+4*η^6+2*η^12)/reciprocalT (η^2),
        4*η^6/reciprocalT (η^2),16*η^4/reciprocalT (η^2)] : Fin 5 → ℝ) i := by
  have hn : reciprocalN (η^2) ≠ 0 := ne_of_gt (reciprocalN_pos η)
  have ht : reciprocalT (η^2) ≠ 0 := ne_of_gt (reciprocalT_pos η)
  intro i; rw [reciprocalState_purity, reciprocalState, block_gap_weights]
  fin_cases i <;> norm_num <;> field_simp <;> ring

/-- Combining the two signed atoms gives the coefficient of `1 - cos (ω t)`. -/
def pairedGapWeight (A : FourLevel) (ω : ℝ) : ℝ :=
  States.operatorGapWeight energy A ω + States.operatorGapWeight energy A (-ω)

theorem block_paired_gap2 (a b c d : ℝ) : pairedGapWeight (block a b c d) 2 = 2*b^2 := by
  norm_num [pairedGapWeight, States.operatorGapWeight, States.gapWeight,
    energy, block, Fin.sum_univ_succ]; ring

theorem block_paired_gap1 (a b c d : ℝ) : pairedGapWeight (block a b c d) 1 = 2*d^2 := by
  norm_num [pairedGapWeight, States.operatorGapWeight, States.gapWeight,
    energy, block, Fin.sum_univ_succ]; ring

/-- Exact physical coefficients in the main family's displayed return losses. -/
theorem main_return_loss_coefficients {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    pairedGapWeight (mainRoot ε) 2 = (1-ε)/10 ∧
    pairedGapWeight (mainRoot ε) 1 = ε/10 ∧
    pairedGapWeight (mainState ε) 2 / trace (mainState ε * mainState ε) =
      9*(1-ε)^2/(34*mainD ε) ∧
    pairedGapWeight (mainState ε) 1 / trace (mainState ε * mainState ε) =
      9*ε^2/(34*mainD ε) := by
  have h1 := mainScale_sq (show 0 ≤ 1-ε by linarith)
  have h2 := mainScale_sq (le_of_lt he)
  have hd : mainD ε ≠ 0 := by have h := (mainD_bounds he he').1; linarith
  simp only [mainState_purity]
  simp only [mainRoot, mainState, block_paired_gap2, block_paired_gap1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]; ring
  · rw [h2]; ring
  · field_simp; ring
  · field_simp; ring

/-- Exact physical coefficients in the reciprocal family's displayed return losses. -/
theorem reciprocal_return_loss_coefficients (η : ℝ) :
    pairedGapWeight (reciprocalRoot η) 2 = 2*η^2/reciprocalN (η^2) ∧
    pairedGapWeight (reciprocalRoot η) 1 = 2*(η^2)^3/reciprocalN (η^2) ∧
    pairedGapWeight (reciprocalState η) 2 / trace (reciprocalState η * reciprocalState η) =
      32*(η^2)^2/reciprocalT (η^2) ∧
    pairedGapWeight (reciprocalState η) 1 / trace (reciprocalState η * reciprocalState η) =
      8*(η^2)^3/reciprocalT (η^2) := by
  have hs := reciprocalScale_sq η
  have hn : reciprocalN (η^2) ≠ 0 := ne_of_gt (reciprocalN_pos η)
  have ht : reciprocalT (η^2) ≠ 0 := ne_of_gt (reciprocalT_pos η)
  simp only [reciprocalState_purity]
  simp only [reciprocalRoot, reciprocalState,
    block_paired_gap2, block_paired_gap1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_pow, hs]; ring
  · rw [mul_pow, hs]; ring
  · field_simp; ring
  · field_simp; ring

theorem reciprocalRoot_eq_scaled_raw (η : ℝ) :
    reciprocalRoot η = (1 / Real.sqrt (reciprocalN (η^2))) • reciprocalRaw η := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [reciprocalRoot, reciprocalRaw, reciprocalScale, block] <;> ring

theorem mainRoot_gap_positive {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (i : Fin 5) :
    0 < States.operatorGapWeight energy (mainRoot ε) (nodes i) := by
  rw [mainRoot_gap_weights he he']
  fin_cases i <;> norm_num <;> linarith

theorem mainState_gap_positive {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (i : Fin 5) :
    0 < States.operatorGapWeight energy (mainState ε) (nodes i) /
      trace (mainState ε * mainState ε) := by
  have hd : 0 < mainD ε := by have h := (mainD_bounds he he').1; linarith
  have h1 : 0 < 1-ε := by linarith
  rw [mainState_gap_weights he he']
  fin_cases i <;> norm_num <;> positivity

theorem reciprocalRoot_gap_positive {η : ℝ} (hη : 0 < η) (i : Fin 5) :
    0 < States.operatorGapWeight energy (reciprocalRoot η) (nodes i) := by
  have hn := reciprocalN_pos η
  rw [reciprocalRoot_gap_weights]
  fin_cases i <;> norm_num <;> positivity

theorem reciprocalState_gap_positive {η : ℝ} (hη : 0 < η) (i : Fin 5) :
    0 < States.operatorGapWeight energy (reciprocalState η) (nodes i) /
      trace (reciprocalState η * reciprocalState η) := by
  have ht := reciprocalT_pos η
  rw [reciprocalState_gap_weights]
  fin_cases i <;> norm_num <;> positivity

/-- Both seeds are supported on exactly the same five commutator frequencies. -/
theorem main_gap_support (ε ω : ℝ) (hm2 : ω ≠ -2) (hm1 : ω ≠ -1)
    (h0 : ω ≠ 0) (hp1 : ω ≠ 1) (hp2 : ω ≠ 2) :
    States.operatorGapWeight energy (mainRoot ε) ω = 0 ∧
    States.operatorGapWeight energy (mainState ε) ω = 0 := by
  constructor <;> apply block_gap_support <;> assumption

theorem reciprocal_gap_support (η ω : ℝ) (hm2 : ω ≠ -2) (hm1 : ω ≠ -1)
    (h0 : ω ≠ 0) (hp1 : ω ≠ 1) (hp2 : ω ≠ 2) :
    States.operatorGapWeight energy (reciprocalRoot η) ω = 0 ∧
    States.operatorGapWeight energy (reciprocalState η) ω = 0 := by
  constructor <;> apply block_gap_support <;> assumption

end Krylov.TemporalStates
