import Krylov.Qubit
import Krylov.OperatorBridge
import Krylov.Purification

/-!
# Density-matrix coefficient hierarchy for a qubit in an energy basis

This file derives the three scalar coefficient inequalities directly from an
arbitrary complex positive semidefinite 2×2 density matrix and its mathlib
positive square root. No Bloch-angle parameterization is assumed. Identifying
the resulting three scalar formulas with all original physical Krylov
constructions still requires the spectral-isometry/evolution bridge.
-/

namespace Krylov.PhysicalQubit
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 2000000

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

def purity (ρ : QubitMatrix) : ℝ := (ρ * ρ).trace.re
def coherence (ρ : QubitMatrix) : ℝ := Complex.normSq (ρ 0 1)
def spreadCoefficient (ρ : QubitMatrix) (hρ : ρ.PosSemidef) : ℝ := 2 * coherence hρ.sqrt
def mixedCoefficient (ρ : QubitMatrix) : ℝ := 2 * coherence ρ / purity ρ
def purifiedCoefficient (ρ : QubitMatrix) : ℝ := 2 * (ρ 0 0).re * (ρ 1 1).re

private theorem hermitian_coordinates {A : QubitMatrix} (hA : A.IsHermitian) :
    (A 0 0).im = 0 ∧ (A 1 1).im = 0 ∧
      (A 1 0).re = (A 0 1).re ∧ (A 1 0).im = -(A 0 1).im := by
  have h00 := hA.coe_re_apply_self 0
  have h11 := hA.coe_re_apply_self 1
  have h10 := hA.apply 1 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (congrArg Complex.im h00).symm
  · simpa using (congrArg Complex.im h11).symm
  · simpa [Complex.star_def] using (congrArg Complex.re h10).symm
  · simpa [Complex.star_def] using (congrArg Complex.im h10).symm

theorem psd_diagonal_nonnegative {A : QubitMatrix} (hA : A.PosSemidef) (i : Fin 2) :
    0 ≤ (A i i).re := by
  have h : 0 ≤ A i i := by
    simpa only [Matrix.mulVec_single_one, ← Pi.single_star, star_one,
      single_dotProduct, one_mul, Matrix.transpose_apply] using hA.2 (Pi.single i 1)
  exact (RCLike.nonneg_iff.mp h).1

theorem psd_determinant_nonnegative {A : QubitMatrix} (hA : A.PosSemidef) :
    0 ≤ A.det.re := by
  have h : 0 ≤ A.det := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    apply Finset.prod_nonneg
    intro i _
    simpa using hA.eigenvalues_nonneg i
  exact (RCLike.nonneg_iff.mp h).1

theorem hermitian_det {A : QubitMatrix} (hA : A.IsHermitian) :
    A.det.re = (A 0 0).re * (A 1 1).re - coherence A := by
  obtain ⟨h00, h11, h10r, h10i⟩ := hermitian_coordinates hA
  simp [Matrix.det_fin_two, coherence, Complex.mul_re, Complex.normSq_apply,
    h00, h11, h10r, h10i]

/-- The PSD determinant supplies the off-diagonal Cauchy--Schwarz inequality. -/
theorem coherence_le_diagonal_product {A : QubitMatrix} (hA : A.PosSemidef) :
    coherence A ≤ (A 0 0).re * (A 1 1).re := by
  have h := psd_determinant_nonnegative hA
  rw [hermitian_det hA.isHermitian] at h
  linarith

theorem purity_expansion {A : QubitMatrix} (hA : A.IsHermitian) :
    purity A = (A 0 0).re ^ 2 + (A 1 1).re ^ 2 + 2 * coherence A := by
  obtain ⟨h00, h11, h10r, h10i⟩ := hermitian_coordinates hA
  simp [purity, coherence, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
    Complex.mul_re, Complex.normSq_apply, h00, h11, h10r, h10i]
  ring

theorem diagonal_sum {ρ : QubitMatrix} (htrace : ρ.trace = 1) :
    (ρ 0 0).re + (ρ 1 1).re = 1 := by
  simpa [Matrix.trace, Fin.sum_univ_succ] using congrArg Complex.re htrace

/-- Every qubit density matrix has purity in `[1/2,1]`, including rank-one
and maximally mixed endpoints. -/
theorem purity_bounds {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    1 / 2 ≤ purity ρ ∧ purity ρ ≤ 1 := by
  have hs := diagonal_sum htrace
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  have hc := coherence_le_diagonal_product hρ
  have hc0 : 0 ≤ coherence ρ := Complex.normSq_nonneg _
  rw [purity_expansion hρ.isHermitian]
  constructor <;> nlinarith [sq_nonneg ((ρ 0 0).re - (ρ 1 1).re)]

/-- Entrywise squaring of a Hermitian two-level matrix. -/
theorem square_offdiagonal {A : QubitMatrix} (hA : A.IsHermitian) :
    (A * A) 0 1 = (((A 0 0).re + (A 1 1).re : ℝ) : ℂ) * A 0 1 := by
  have hprod : (A * A) 0 1 = A 0 0 * A 0 1 + A 0 1 * A 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hprod]
  conv_lhs =>
    rw [← hA.coe_re_apply_self 0, ← hA.coe_re_apply_self 1]
  change ((A 0 0).re : ℂ) * A 0 1 + A 0 1 * ((A 1 1).re : ℂ) = _
  push_cast
  ring

theorem square_coherence {A : QubitMatrix} (hA : A.IsHermitian) :
    coherence (A * A) = ((A 0 0).re + (A 1 1).re) ^ 2 * coherence A := by
  unfold coherence
  rw [square_offdiagonal hA, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- The squared trace of the positive square root is at least one. -/
theorem sqrt_trace_square_ge_one {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) :
    1 ≤ ((hρ.sqrt 0 0).re + (hρ.sqrt 1 1).re) ^ 2 := by
  have hQ := hρ.posSemidef_sqrt
  have hc := coherence_le_diagonal_product hQ
  have hnorm : purity hρ.sqrt = 1 := by
    unfold purity
    rw [hρ.sqrt_mul_self, htrace]
    rfl
  rw [purity_expansion hQ.isHermitian] at hnorm
  nlinarith

/-- The physical square-root seed carries no more off-diagonal squared mass
than the unnormalized density itself in dimension two. -/
theorem sqrt_coherence_le {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) : coherence hρ.sqrt ≤ coherence ρ := by
  have hs := sqrt_trace_square_ge_one hρ htrace
  have hc0 : 0 ≤ coherence hρ.sqrt := Complex.normSq_nonneg _
  have hm := mul_nonneg (sub_nonneg.mpr hs) hc0
  have he := square_coherence hρ.posSemidef_sqrt.isHermitian
  rw [hρ.sqrt_mul_self] at he
  nlinarith

/-- Direct physical coefficient ordering, without an assumed scalar
parameterization or a nonzero-coherence condition. -/
theorem coefficient_hierarchy {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) :
    0 ≤ spreadCoefficient ρ hρ ∧
    spreadCoefficient ρ hρ ≤ mixedCoefficient ρ ∧
    mixedCoefficient ρ ≤ purifiedCoefficient ρ ∧
    purifiedCoefficient ρ ≤ 1 / 2 := by
  have hs := diagonal_sum htrace
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  have ha := psd_diagonal_nonnegative hρ 0
  have hb := psd_diagonal_nonnegative hρ 1
  have hr0 : 0 ≤ coherence ρ := Complex.normSq_nonneg _
  have hr := coherence_le_diagonal_product hρ
  have hab : (ρ 0 0).re * (ρ 1 1).re ≤ 1 / 4 := by
    nlinarith [sq_nonneg ((ρ 0 0).re - (ρ 1 1).re)]
  obtain ⟨hPlo, hPhi⟩ := purity_bounds hρ htrace
  have hPpos : 0 < purity ρ := by linarith
  have hP : purity ρ = 1 - 2 * (ρ 0 0).re * (ρ 1 1).re + 2 * coherence ρ := by
    rw [purity_expansion hρ.isHermitian]
    nlinarith
  have hQ0 : 0 ≤ coherence hρ.sqrt := Complex.normSq_nonneg _
  have hQr := sqrt_coherence_le hρ htrace
  refine ⟨by unfold spreadCoefficient; positivity, ?_, ?_, ?_⟩
  · unfold spreadCoefficient mixedCoefficient
    apply (le_div_iff₀ hPpos).2
    nlinarith [mul_nonneg hQ0 (sub_nonneg.mpr hPhi)]
  · unfold mixedCoefficient purifiedCoefficient
    apply (div_le_iff₀ hPpos).2
    rw [hP]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (show 0 ≤ 1 - 2 * (ρ 0 0).re * (ρ 1 1).re by nlinarith)]
  · unfold purifiedCoefficient
    nlinarith

/-- A scalar-complexity hierarchy whose parameters are computed from an
arbitrary PSD trace-one qubit matrix, its actual positive square root, and
its actual purity. -/
theorem density_formula_hierarchy {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (ω t : ℝ) :
    Qubit.threeAtom (spreadCoefficient ρ hρ) (ω * t) ≤
      Qubit.threeAtom (mixedCoefficient ρ) (ω * t) ∧
    Qubit.threeAtom (mixedCoefficient ρ) (ω * t) ≤
      Qubit.threeAtom (purifiedCoefficient ρ) (ω * t) := by
  obtain ⟨hS0, hSK, hKI, hI1⟩ := coefficient_hierarchy hρ htrace
  have hK1 := le_trans hKI hI1
  have hS1 := le_trans hSK hK1
  exact ⟨Qubit.threeAtom_mono hS1 hK1 hSK _, Qubit.threeAtom_mono hK1 hI1 hKI _⟩

/-- Ordered distinct-energy gap table; the first and last gaps may appear in
either numerical order without affecting the symmetric weights. -/
def gapNodes (E : Fin 2 → ℝ) : Fin 3 → ℝ := ![E 0 - E 1, 0, E 1 - E 0]

def threeAtomWeights (μ : ℝ) : Fin 3 → ℝ := ![μ / 2, 1 - μ, μ / 2]

def rawGapTable (A : QubitMatrix) : Fin 3 → ℝ :=
  ![Complex.normSq (A 0 1), Complex.normSq (A 0 0) + Complex.normSq (A 1 1),
    Complex.normSq (A 1 0)]

/-- Exact grouping of matrix entries into the three commutator gaps. -/
theorem operator_gap_table (E : Fin 2 → ℝ) (hE : E 0 ≠ E 1) (A : QubitMatrix) :
    (fun i => OperatorBridge.gapWeight E A (gapNodes E i)) = rawGapTable A := by
  have hd : E 0 - E 1 ≠ 0 := sub_ne_zero.mpr hE
  have hd' : E 1 - E 0 ≠ 0 := sub_ne_zero.mpr hE.symm
  have hm : E 1 - E 0 ≠ E 0 - E 1 := by intro h; apply hE; linarith
  ext i
  fin_cases i <;>
    simp [OperatorBridge.gapWeight, gapNodes, rawGapTable, Fin.sum_univ_succ,
      hd, hd', hm, hE, hE.symm, Ne.symm hd, Ne.symm hd', Ne.symm hm]

/-- Hermitian symmetry and the actual Hilbert--Schmidt purity fix the central
weight as well as the two equal side weights. -/
theorem hermitian_gap_table {A : QubitMatrix} (hA : A.IsHermitian) :
    rawGapTable A = ![coherence A, purity A - 2 * coherence A, coherence A] := by
  obtain ⟨h00, h11, h10r, h10i⟩ := hermitian_coordinates hA
  rw [purity_expansion hA]
  ext i
  fin_cases i <;>
    simp [rawGapTable, coherence, Complex.normSq_apply, h00, h11, h10r, h10i]
  all_goals ring

/-- The positive square-root seed is normalized in Hilbert--Schmidt norm. -/
theorem sqrt_seed_normalized {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) : purity hρ.sqrt = 1 := by
  unfold purity
  rw [hρ.sqrt_mul_self, htrace]
  rfl

theorem spread_gap_table {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (E : Fin 2 → ℝ) (hE : E 0 ≠ E 1) :
    (fun i => OperatorBridge.gapWeight E hρ.sqrt (gapNodes E i)) =
      threeAtomWeights (spreadCoefficient ρ hρ) := by
  rw [operator_gap_table E hE, hermitian_gap_table hρ.posSemidef_sqrt.isHermitian,
    sqrt_seed_normalized hρ htrace]
  ext i
  fin_cases i <;> simp [threeAtomWeights, spreadCoefficient]

theorem mixed_gap_table {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (E : Fin 2 → ℝ) (hE : E 0 ≠ E 1) :
    (fun i => OperatorBridge.gapWeight E ρ (gapNodes E i) / purity ρ) =
      threeAtomWeights (mixedCoefficient ρ) := by
  have hP : purity ρ ≠ 0 := by have := (purity_bounds hρ htrace).1; linarith
  have hg := congrFun (operator_gap_table E hE ρ)
  have hh := congrFun (hermitian_gap_table hρ.isHermitian)
  ext i
  fin_cases i <;> simp [hg, hh, threeAtomWeights, mixedCoefficient] <;> field_simp <;> ring

/-- The lifted I-purification's energy row weights are the actual density
matrix diagonal, derived from the positive square root rather than assumed. -/
theorem sqrt_row_weight {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (i : Fin 2) :
    Purification.rowWeight hρ.sqrt i = (ρ i i).re := by
  rw [Purification.rowWeight_eq_density_diagonal,
    hρ.posSemidef_sqrt.isHermitian.eq, hρ.sqrt_mul_self]

theorem purified_gap_table {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (E : Fin 2 → ℝ) (hE : E 0 ≠ E 1) :
    (fun i => Purification.pureGapWeight E hρ.sqrt (gapNodes E i)) =
      threeAtomWeights (purifiedCoefficient ρ) := by
  have hd : E 0 - E 1 ≠ 0 := sub_ne_zero.mpr hE
  have hd' : E 1 - E 0 ≠ 0 := sub_ne_zero.mpr hE.symm
  have hm : E 1 - E 0 ≠ E 0 - E 1 := by intro h; apply hE; linarith
  have hs := diagonal_sum htrace
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  ext i
  fin_cases i <;>
    simp [Purification.pure_gap_difference_convolution, sqrt_row_weight hρ,
      gapNodes, threeAtomWeights, purifiedCoefficient, Fin.sum_univ_succ,
      hd, hd', hm, hE, hE.symm, Ne.symm hd, Ne.symm hd', Ne.symm hm] <;> nlinarith

end
end Krylov.PhysicalQubit
