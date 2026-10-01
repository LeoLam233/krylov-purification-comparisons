import Krylov.PhysicalQubitCV

/-! The source qubit parameters are obtained from the actual density eigenbasis.
The polar angle is defined by its squared overlaps with the energy basis, and
all three physical coherence coefficients are identified with the source formulas. -/
namespace Krylov.QubitParameterization
open Matrix PhysicalQubit UniversalQubit PhysicalQubitCV
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 800000

def overlap (U : QubitMatrix) : ℝ := Complex.normSq (U 0 0)
def polarAngle (U : QubitMatrix) : ℝ := Real.arccos (2 * overlap U - 1)

lemma unitary_row_norm (U : QubitMatrix) (hU : U * Uᴴ = 1) (i : Fin 2) :
    Complex.normSq (U i 0) + Complex.normSq (U i 1) = 1 := by
  have h := congrArg Complex.re (congrFun (congrFun hU i) i)
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
    Complex.mul_re, Complex.normSq_apply] using h

lemma unitary_col_norm (U : QubitMatrix) (hU : Uᴴ * U = 1) (i : Fin 2) :
    Complex.normSq (U 0 i) + Complex.normSq (U 1 i) = 1 := by
  have h := congrArg Complex.re (congrFun (congrFun hU i) i)
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
    Complex.mul_re, Complex.normSq_apply] using h

theorem overlap_bounds (U : QubitMatrix) (hU : U * Uᴴ = 1) :
    overlap U ∈ Set.Icc (0:ℝ) 1 := by
  have h := unitary_row_norm U hU 0
  have hn := Complex.normSq_nonneg (U 0 1)
  exact ⟨Complex.normSq_nonneg _, by dsimp [overlap]; linarith⟩

lemma cos_polarAngle (U : QubitMatrix) (hU : U * Uᴴ = 1) :
    Real.cos (polarAngle U) = 2 * overlap U - 1 := by
  obtain ⟨h0,h1⟩ := overlap_bounds U hU
  exact Real.cos_arccos (by linarith) (by linarith)

/-- The angle describes the actual basis transition, including arbitrary
complex phases: diagonal squared overlaps are cos²(θ/2), off-diagonal
squared overlaps are sin²(θ/2). -/
theorem polarAngle_basis_overlaps (U : QubitMatrix)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    polarAngle U ∈ Set.Icc (0:ℝ) Real.pi ∧
    Complex.normSq (U 0 0) = Real.cos (polarAngle U/2)^2 ∧
    Complex.normSq (U 0 1) = Real.sin (polarAngle U/2)^2 ∧
    Complex.normSq (U 1 0) = Real.sin (polarAngle U/2)^2 ∧
    Complex.normSq (U 1 1) = Real.cos (polarAngle U/2)^2 := by
  have hc := cos_polarAngle U hU
  have hd := Real.cos_two_mul (polarAngle U/2)
  rw [show 2*(polarAngle U/2)=polarAngle U by ring] at hd
  have ht := Real.sin_sq_add_cos_sq (polarAngle U/2)
  have hr0 := unitary_row_norm U hU 0
  have hr1 := unitary_row_norm U hU 1
  have hv0 := unitary_col_norm U hU' 0
  dsimp [overlap] at hc
  refine ⟨⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩,?_,?_,?_,?_⟩ <;> nlinarith

def contrast {ρ : QubitMatrix} (hρ : ρ.PosSemidef) : ℝ :=
  (hρ.isHermitian.eigenvalues 0 - hρ.isHermitian.eigenvalues 1)^2
def angleParameter {ρ : QubitMatrix} (hρ : ρ.PosSemidef) : ℝ :=
  Real.cos (polarAngle (energyBasis hρ.isHermitian))^2

lemma eigenvalue_sum {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    hρ.isHermitian.eigenvalues 0 + hρ.isHermitian.eigenvalues 1 = 1 := by
  have ht := changeBasis_trace (energyBasis hρ.isHermitian) ρ
    (energyBasis_unitary_reverse hρ.isHermitian)
  rw [hamiltonian_coordinates,htr] at ht
  simpa [OperatorBridge.hamiltonian,Matrix.trace,Fin.sum_univ_succ] using congrArg Complex.re ht

lemma eigenvalue_det {ρ : QubitMatrix} (hρ : ρ.PosSemidef) :
    ρ.det.re = hρ.isHermitian.eigenvalues 0 * hρ.isHermitian.eigenvalues 1 := by
  rw [hρ.isHermitian.det_eq_prod_eigenvalues]
  simp [Fin.prod_univ_succ]

lemma spectral_diagonal {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (i : Fin 2) :
    (ρ i i).re = hρ.isHermitian.eigenvalues 0 * Complex.normSq (energyBasis hρ.isHermitian i 0) +
      hρ.isHermitian.eigenvalues 1 * Complex.normSq (energyBasis hρ.isHermitian i 1) := by
  have hs := congrArg Complex.re (congrFun (congrFun hρ.isHermitian.spectral_theorem i) i)
  simp [energyBasis, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
    Complex.mul_re, Complex.mul_im, Complex.normSq_apply, RCLike.ofReal,
    Algebra.cast, Complex.coe_algebraMap] at hs ⊢
  linear_combination hs

theorem source_parameters_bounds {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    contrast hρ ∈ Set.Icc (0:ℝ) 1 ∧ angleParameter hρ ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨Qubit.eigenvalue_contrast_bounds (hρ.eigenvalues_nonneg 0)
    (hρ.eigenvalues_nonneg 1) (eigenvalue_sum hρ htr),sq_nonneg _,?_⟩
  dsimp [angleParameter]
  nlinarith [Real.sin_sq_add_cos_sq (polarAngle (energyBasis hρ.isHermitian)),
    sq_nonneg (Real.sin (polarAngle (energyBasis hρ.isHermitian)))]

lemma diagonal_difference {ρ : QubitMatrix} (hρ : ρ.PosSemidef) :
    (ρ 0 0).re - (ρ 1 1).re =
      (hρ.isHermitian.eigenvalues 0-hρ.isHermitian.eigenvalues 1)*
        Real.cos (polarAngle (energyBasis hρ.isHermitian)) := by
  have h0 := spectral_diagonal hρ 0
  have h1 := spectral_diagonal hρ 1
  have hr0 := unitary_row_norm _ (energyBasis_unitary_reverse hρ.isHermitian) 0
  have hr1 := unitary_row_norm _ (energyBasis_unitary_reverse hρ.isHermitian) 1
  have hc0 := unitary_col_norm _ (energyBasis_unitary hρ.isHermitian) 0
  rw [cos_polarAngle _ (energyBasis_unitary_reverse hρ.isHermitian)]
  dsimp [overlap]
  rw [h0,h1]
  linear_combination
    -(hρ.isHermitian.eigenvalues 0-hρ.isHermitian.eigenvalues 1)*hc0 +
    hρ.isHermitian.eigenvalues 1*hr0 - hρ.isHermitian.eigenvalues 1*hr1

lemma rootParameter_eq_sqrt {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    rootParameter hρ = Real.sqrt (1-contrast hρ) := by
  have hs := eigenvalue_sum hρ htr
  have hd := density_det_root hρ
  rw [eigenvalue_det hρ] at hd
  have hy := parameter_nonnegative hρ
  symm
  apply (Real.sqrt_eq_iff_eq_sq (sub_nonneg.mpr (source_parameters_bounds hρ htr).1.2) hy).2
  dsimp [contrast,rootParameter]
  nlinarith [sq_nonneg (hρ.isHermitian.eigenvalues 0+hρ.isHermitian.eigenvalues 1-1)]

lemma physical_purity {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    purity ρ = (1+contrast hρ)/2 := by
  rw [purity_det_identity hρ htr,eigenvalue_det hρ]
  have hs := eigenvalue_sum hρ htr
  dsimp [contrast]
  nlinarith [congrArg (fun x : ℝ => x^2) hs]

lemma physical_coherence {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    4*coherence ρ = contrast hρ*(1-angleParameter hρ) := by
  have hsum := diagonal_sum htr
  have hdiff := diagonal_difference hρ
  have hp := purity_expansion hρ.isHermitian
  rw [physical_purity hρ htr] at hp
  have hd2 := congrArg (fun x : ℝ => x^2) hdiff
  dsimp [contrast,angleParameter] at *
  nlinarith [congrArg (fun x : ℝ => x^2) hsum]

/-- Literal source eq:qubit-mus, with z given by actual density eigenvalues
and c the squared cosine of the actual eigenbasis polar rotation. No
nonstationarity, rank, or distinct-eigenvalue assumption is required. -/
theorem physical_coefficients {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    spreadCoefficient ρ hρ = Qubit.muS (contrast hρ) (angleParameter hρ) ∧
    mixedCoefficient ρ = Qubit.muK (contrast hρ) (angleParameter hρ) ∧
    purifiedCoefficient ρ = Qubit.muI (contrast hρ) (angleParameter hρ) := by
  have hz := (source_parameters_bounds hρ htr).1
  have hc := physical_coherence hρ htr
  have hr := coherence_parameter hρ htr
  rw [rootParameter_eq_sqrt hρ htr] at hr
  have hs := Real.sq_sqrt (sub_nonneg.mpr hz.2)
  have hnonneg := Real.sqrt_nonneg (1-contrast hρ)
  have hden : 1+Real.sqrt (1-contrast hρ) ≠ 0 := by positivity
  have hz0 := hz.1
  have hzden : 1+contrast hρ ≠ 0 := by positivity
  refine ⟨?_,?_,?_⟩
  · unfold spreadCoefficient Qubit.muS
    apply (mul_left_cancel₀ hden)
    linear_combination hc/2 - 2*hr + ((1-angleParameter hρ)/2)*hs
  · unfold mixedCoefficient Qubit.muK
    rw [physical_purity hρ htr]
    field_simp
    nlinarith
  · have hsum := diagonal_sum htr
    have hdiff := diagonal_difference hρ
    have hd2 := congrArg (fun x : ℝ => x^2) hdiff
    unfold purifiedCoefficient Qubit.muI
    dsimp [contrast,angleParameter] at *
    nlinarith [congrArg (fun x : ℝ => x^2) hsum]


lemma squareRoot_sum {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    (Real.sqrt (hρ.isHermitian.eigenvalues 0)+Real.sqrt (hρ.isHermitian.eigenvalues 1))^2 =
      1+rootParameter hρ := by
  rw [rootParameter_eq_sqrt hρ htr]
  have hp := hρ.eigenvalues_nonneg 0
  have hq := hρ.eigenvalues_nonneg 1
  have hs := eigenvalue_sum hρ htr
  have hb := Qubit.eigenvalue_sqrt_bridge hp hq hs
  dsimp [contrast]
  nlinarith [Real.sq_sqrt hp,Real.sq_sqrt hq]

lemma eigenvalue_purity {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    purity ρ = (hρ.isHermitian.eigenvalues 0)^2+(hρ.isHermitian.eigenvalues 1)^2 := by
  rw [physical_purity hρ htr]
  have hs := eigenvalue_sum hρ htr
  dsimp [contrast]
  nlinarith [congrArg (fun x : ℝ => x^2) hs]

/-- First literal identity in eq:qubit-order, with its source's nonzero
spread coefficient premise. The eigenvalues are those of the actual density. -/
theorem coefficient_ratio_eigenvalues {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hS : spreadCoefficient ρ hρ ≠ 0) :
    mixedCoefficient ρ / spreadCoefficient ρ hρ =
      (Real.sqrt (hρ.isHermitian.eigenvalues 0)+Real.sqrt (hρ.isHermitian.eigenvalues 1))^2 /
        ((hρ.isHermitian.eigenvalues 0)^2+(hρ.isHermitian.eigenvalues 1)^2) := by
  have hq : coherence hρ.sqrt ≠ 0 := by
    intro hz
    apply hS
    simp [spreadCoefficient,hz]
  have hP : purity ρ ≠ 0 := by have := (purity_bounds hρ htr).1; linarith
  rw [squareRoot_sum hρ htr,← eigenvalue_purity hρ htr]
  unfold mixedCoefficient spreadCoefficient
  rw [coherence_parameter hρ htr]
  field_simp
  <;> ring

/-- Second literal identity in eq:qubit-order, valid at every endpoint. -/
theorem coefficient_difference {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    purifiedCoefficient ρ-mixedCoefficient ρ =
      ((1-contrast hρ)*(1+contrast hρ*angleParameter hρ))/(2*(1+contrast hρ)) := by
  obtain ⟨hS,hK,hI⟩ := physical_coefficients hρ htr
  rw [hK,hI]
  have hz := (source_parameters_bounds hρ htr).1.1
  have hn : 1+contrast hρ ≠ 0 := by positivity
  unfold Qubit.muI Qubit.muK
  field_simp
  <;> ring

theorem displayed_coefficient_order {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) (hS : spreadCoefficient ρ hρ ≠ 0) :
    1 ≤ (Real.sqrt (hρ.isHermitian.eigenvalues 0)+Real.sqrt (hρ.isHermitian.eigenvalues 1))^2 /
      ((hρ.isHermitian.eigenvalues 0)^2+(hρ.isHermitian.eigenvalues 1)^2) ∧
    0 ≤ ((1-contrast hρ)*(1+contrast hρ*angleParameter hρ))/(2*(1+contrast hρ)) := by
  obtain ⟨h0,hSK,hKI,_⟩ := coefficient_hierarchy hρ htr
  rw [← coefficient_ratio_eigenvalues hρ htr hS,← coefficient_difference hρ htr]
  exact ⟨(one_le_div (lt_of_le_of_ne h0 (Ne.symm hS))).2 hSK,sub_nonneg.mpr hKI⟩

/-- A density eigenbasis in the original physical coordinates, constructed
from the density's diagonalization in the Hamiltonian energy basis. -/
def physicalDensityBasis {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) : QubitMatrix :=
  energyBasis hH * energyBasis (coordinateDensity_posSemidef hH hρ).isHermitian

lemma physicalDensityBasis_unitary {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) :
    (physicalDensityBasis hH hρ)ᴴ * physicalDensityBasis hH hρ = 1 ∧
    physicalDensityBasis hH hρ * (physicalDensityBasis hH hρ)ᴴ = 1 := by
  let U := energyBasis hH
  let V := energyBasis (coordinateDensity_posSemidef hH hρ).isHermitian
  constructor
  · change (U*V)ᴴ*(U*V)=1
    calc
      _ = Vᴴ*(Uᴴ*U)*V := by simp [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [energyBasis_unitary,Matrix.mul_one,energyBasis_unitary]
  · change (U*V)*(U*V)ᴴ=1
    calc
      _ = U*(V*Vᴴ)*Uᴴ := by simp [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [energyBasis_unitary_reverse,Matrix.mul_one,energyBasis_unitary_reverse]

lemma physicalDensityBasis_diagonalizes {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) :
    UnitaryCovariance.changeBasis (physicalDensityBasis hH hρ) ρ =
      OperatorBridge.hamiltonian (coordinateDensity_posSemidef hH hρ).isHermitian.eigenvalues := by
  simpa [physicalDensityBasis,UnitaryCovariance.changeBasis,coordinateDensity,
    Matrix.conjTranspose_mul,Matrix.mul_assoc] using
      hamiltonian_coordinates (coordinateDensity_posSemidef hH hρ).isHermitian

lemma physical_basis_transition {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) :
    (energyBasis hH)ᴴ * physicalDensityBasis hH hρ =
      energyBasis (coordinateDensity_posSemidef hH hρ).isHermitian := by
  unfold physicalDensityBasis
  rw [← Matrix.mul_assoc,energyBasis_unitary,Matrix.one_mul]

/-- The c parameter used in the physical formulas is the squared cosine of
an angle whose four half-angle overlaps are the ACTUAL transition between
an energy eigenbasis and a density eigenbasis in the original coordinates. -/
theorem physical_polar_angle {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) :
    let U := (energyBasis hH)ᴴ * physicalDensityBasis hH hρ
    angleParameter (coordinateDensity_posSemidef hH hρ) = Real.cos (polarAngle U)^2 ∧
    polarAngle U ∈ Set.Icc (0:ℝ) Real.pi ∧
    Complex.normSq (U 0 0) = Real.cos (polarAngle U/2)^2 ∧
    Complex.normSq (U 0 1) = Real.sin (polarAngle U/2)^2 ∧
    Complex.normSq (U 1 0) = Real.sin (polarAngle U/2)^2 ∧
    Complex.normSq (U 1 1) = Real.cos (polarAngle U/2)^2 := by
  dsimp only
  rw [physical_basis_transition]
  exact ⟨rfl,polarAngle_basis_overlaps _ (energyBasis_unitary_reverse _)
    (energyBasis_unitary _)⟩

/-- Physical coefficient formulas for an arbitrary Hermitian Hamiltonian,
with the actual eigenvalue contrast and actual relative polar angle above. -/
theorem energy_basis_coefficients {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    let q := coordinateDensity_posSemidef hH hρ
    spreadCoefficient (coordinateDensity hH ρ) q = Qubit.muS (contrast q) (angleParameter q) ∧
    mixedCoefficient (coordinateDensity hH ρ) = Qubit.muK (contrast q) (angleParameter q) ∧
    purifiedCoefficient (coordinateDensity hH ρ) = Qubit.muI (contrast q) (angleParameter q) :=
  physical_coefficients _ (coordinateDensity_trace hH htr)

end
end Krylov.QubitParameterization
