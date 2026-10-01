import Krylov.QubitSourceAPI
import Krylov.WitnessSourceAPI
import Krylov.QubitRange

/-! Source-level consequences in one common generic GS API. -/
namespace Krylov.SourceProse
open Matrix OperatorBridge UnitaryCovariance PhysicalQubit UniversalQubit
open QubitSourceAPI PhysicalQubitCV RestrictedCV
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 1000000

def LowerFailure (n : ℕ) : Prop :=
  ∃ (H ρ : Operator (Fin n)) (hρ : ρ.PosSemidef), H.IsHermitian ∧ ρ.trace=1 ∧
    ∃ t : ℝ, PhysicalCurvatureNecessary.mixedComplexity H ρ t <
      PurificationBranches.spread (PurificationBranches.generatorU H) (PurificationBranches.seed hρ) t

def UpperFailure (n : ℕ) : Prop :=
  ∃ (H ρ : Operator (Fin n)) (hρ : ρ.PosSemidef), H.IsHermitian ∧ ρ.trace=1 ∧
    ∃ t : ℝ, PurificationBranches.pureOperator (PurificationBranches.generatorI H)
      (PurificationBranches.seed hρ) t < PhysicalCurvatureNecessary.mixedComplexity H ρ t

theorem lower_failure_three : LowerFailure 3 := by
  refine ⟨States.hL.map Complex.ofReal,States.rhoL.map Complex.ofReal,
    complex_rhoL_posDef.posSemidef,?_,WitnessSourceAPI.complex_trace_one _ States.rhoL_trace,
    Real.pi,?_⟩
  · rw [WitnessSourceAPI.left_hamiltonian]
    exact MatrixGSBridge.diagonal_hermitian _
  · rw [WitnessSourceAPI.prop_left.1,WitnessSourceAPI.prop_left.2.1]
    norm_num

theorem upper_failure_three : UpperFailure 3 := by
  refine ⟨States.hR.map Complex.ofReal,States.rhoR.map Complex.ofReal,
    complex_rhoR_posDef.posSemidef,WitnessSourceAPI.right_hermitian,
    WitnessSourceAPI.complex_trace_one _ States.rhoR_trace,Real.pi/3,?_⟩
  rw [WitnessSourceAPI.prop_right.1,WitnessSourceAPI.prop_right.2.1]
  norm_num

theorem lower_failure_dimension {n : ℕ} (hn : LowerFailure n) : 3 ≤ n := by
  obtain ⟨H,ρ,hρ,hH,htr,t,ht⟩ := hn
  by_contra hn
  have hn' : n < 3 := by omega
  interval_cases n
  · have hf : (0:ℂ)=1 := by simpa [Matrix.trace] using htr
    norm_num at hf
  · obtain ⟨hS,hM,_⟩ := dimension_one_zero hH hρ htr t
    rw [hS,hM] at ht
    exact lt_irrefl _ ht
  · exact (not_lt_of_ge (source_hierarchy hH hρ htr t).1) ht

theorem upper_failure_dimension {n : ℕ} (hn : UpperFailure n) : 3 ≤ n := by
  obtain ⟨H,ρ,hρ,hH,htr,t,ht⟩ := hn
  by_contra hn
  have hn' : n < 3 := by omega
  interval_cases n
  · have hf : (0:ℂ)=1 := by simpa [Matrix.trace] using htr
    norm_num at hf
  · obtain ⟨_,hM,hP⟩ := dimension_one_zero hH hρ htr t
    rw [hP,hM] at ht
    exact lt_irrefl _ ht
  · exact (not_lt_of_ge (source_hierarchy hH hρ htr t).2) ht

/-- Physical dimension three is minimal for failure of EACH side, with
the d1/d2 exclusions and d3 witnesses all expressed in the same generic GS API. -/
theorem minimal_physical_dimension :
    IsLeast {n : ℕ | LowerFailure n} 3 ∧ IsLeast {n : ℕ | UpperFailure n} 3 :=
  ⟨⟨lower_failure_three,fun _ hn => lower_failure_dimension hn⟩,
    ⟨upper_failure_three,fun _ hn => upper_failure_dimension hn⟩⟩

/-- The final source qubit-CV package includes the actual generic GS ratio
identification, continuous removable extension, positivity and the three
measure-theoretic bounds in one kernel theorem. -/
theorem source_cv_with_identification {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hc : H*ρ-ρ*H ≠ 0)
    (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] :
    (∀ t : ℝ, Real.sin (energyGap hH*t/2) ≠ 0 →
      extendedRatio hH hρ t =
        PurificationBranches.spread (PurificationBranches.generatorU H)
          (PurificationBranches.seed hρ) t / PhysicalCurvatureNecessary.mixedComplexity H ρ t ∧
      extendedReciprocal hH hρ t = PhysicalCurvatureNecessary.mixedComplexity H ρ t /
        PurificationBranches.spread (PurificationBranches.generatorU H) (PurificationBranches.seed hρ) t ∧
      extendedPurityRatio hH hρ t = PhysicalQubit.purity ρ *
        (PhysicalCurvatureNecessary.mixedComplexity H ρ t /
          PurificationBranches.spread (PurificationBranches.generatorU H) (PurificationBranches.seed hρ) t)) ∧
    (∀ t, 0 < extendedRatio hH hρ t ∧ 0 < extendedReciprocal hH hρ t ∧
      0 < extendedPurityRatio hH hρ t) ∧
    Continuous (extendedRatio hH hρ) ∧ Continuous (extendedReciprocal hH hρ) ∧
    Continuous (extendedPurityRatio hH hρ) ∧
    coefficientVariation (extendedRatio hH hρ) ν ≤ (kappaStar-1)/(2*Real.sqrt kappaStar) ∧
    coefficientVariation (extendedReciprocal hH hρ) ν ≤ (kappaStar-1)/(2*Real.sqrt kappaStar) ∧
    coefficientVariation (extendedPurityRatio hH hρ) ν ≤ (kappaStar-1)/(2*Real.sqrt kappaStar) := by
  refine ⟨fun t ht => source_ratio_eq hH hρ htr hc ht,?_,source_cv hH hρ htr hc ν⟩
  intro t
  have hr := extendedRatio_positive hH hρ htr (nonstationary_of_commutator_ne hH hρ htr hc) t
  have hp : 0 < PhysicalQubit.purity ρ := by have := (purity_bounds hρ htr).1; linarith
  exact ⟨hr,one_div_pos.mpr hr,mul_pos hp (one_div_pos.mpr hr)⟩

/-- An exact rational enclosure certifies the source's displayed decimal
0.1375633885 (rounded to ten digits after the decimal point). -/
theorem cv_constant_decimal :
    (13756338852:ℝ)/100000000000 < (kappaStar-1)/(2*Real.sqrt kappaStar) ∧
    (kappaStar-1)/(2*Real.sqrt kappaStar) < (13756338853:ℝ)/100000000000 := by
  have h7 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7)
  have h7n := Real.sqrt_nonneg 7
  have h7l : (2645751311064590:ℝ)/1000000000000000 < Real.sqrt 7 := by nlinarith
  have h7u : Real.sqrt 7 < (2645751311064591:ℝ)/1000000000000000 := by nlinarith
  have hk : 0 < kappaStar := lt_trans (by norm_num) kappaStar_gt_one
  have hr := Real.sq_sqrt hk.le
  have hrn := Real.sqrt_nonneg kappaStar
  have hrl : (1146980886815664:ℝ)/1000000000000000 < Real.sqrt kappaStar := by
    unfold kappaStar at *
    nlinarith
  have hru : Real.sqrt kappaStar < (1146980886815666:ℝ)/1000000000000000 := by
    unfold kappaStar at *
    nlinarith
  have hd : 0 < 2*Real.sqrt kappaStar := by positivity
  constructor
  · apply (lt_div_iff₀ hd).2
    unfold kappaStar at *
    nlinarith
  · apply (div_lt_iff₀ hd).2
    unfold kappaStar at *
    nlinarith


/-- Concrete commuting maximally mixed density and a gap-one Hamiltonian. -/
def stationaryDensity : QubitMatrix := Matrix.diagonal (fun _ => (1/2:ℂ))
def stationaryHamiltonian : QubitMatrix := OperatorBridge.hamiltonian ![0,1]

lemma stationaryDensity_psd : stationaryDensity.PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  apply RCLike.nonneg_iff.mpr
  norm_num

lemma stationaryDensity_trace : stationaryDensity.trace=1 := by
  norm_num [stationaryDensity,Matrix.trace,Fin.sum_univ_succ]

lemma stationaryHamiltonian_psd : stationaryHamiltonian.PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [OperatorBridge.hamiltonian]

lemma stationaryHamiltonian_trace : stationaryHamiltonian.trace=1 := by
  norm_num [stationaryHamiltonian,OperatorBridge.hamiltonian,Matrix.trace,Fin.sum_univ_succ]

lemma stationaryDensity_scalar : stationaryDensity=(1/2:ℂ) • (1:QubitMatrix) := by
  ext i j
  by_cases h : i=j <;> simp [stationaryDensity,Matrix.one_apply,Matrix.diagonal,h]

lemma stationaryDensity_coordinates {H : QubitMatrix} (hH : H.IsHermitian) :
    coordinateDensity hH stationaryDensity=stationaryDensity := by
  calc
    _ = changeBasis (energyBasis hH) ((1/2:ℂ) • (1:QubitMatrix)) := by
      rw [← stationaryDensity_scalar]; rfl
    _ = (1/2:ℂ) • (1:QubitMatrix) := by
      rw [changeBasis_smul]
      congr 1
      simp [changeBasis,energyBasis_unitary]
    _ = stationaryDensity := stationaryDensity_scalar.symm

lemma stationaryHamiltonian_gap :
    energyGap stationaryHamiltonian_psd.isHermitian=1 ∨
      energyGap stationaryHamiltonian_psd.isHermitian= -1 := by
  have hs := QubitParameterization.eigenvalue_sum stationaryHamiltonian_psd stationaryHamiltonian_trace
  have hd := QubitParameterization.eigenvalue_det stationaryHamiltonian_psd
  have hd0 : stationaryHamiltonian.det.re=0 := by
    norm_num [stationaryHamiltonian,OperatorBridge.hamiltonian,Matrix.det_fin_two]
  rw [hd0] at hd
  have hg : (energyGap stationaryHamiltonian_psd.isHermitian)^2=1 := by
    unfold energyGap
    nlinarith [congrArg (fun x : ℝ => x^2) hs]
  exact (sq_eq_one_iff).mp hg

/-- A stationary mixed density can have a nonstationary I-purification:
its U*-spread and mixed complexity are zero at every time, whereas its
actual I-purified operator complexity is exactly two at π. -/
theorem stationary_mixed_nonstationary_purification :
    (∀ t : ℝ,
      PurificationBranches.spread (PurificationBranches.generatorU stationaryHamiltonian)
        (PurificationBranches.seed stationaryDensity_psd) t=0 ∧
      PhysicalCurvatureNecessary.mixedComplexity stationaryHamiltonian stationaryDensity t=0) ∧
    PurificationBranches.pureOperator (PurificationBranches.generatorI stationaryHamiltonian)
      (PurificationBranches.seed stationaryDensity_psd) Real.pi=2 := by
  let hH := stationaryHamiltonian_psd.isHermitian
  have hc : HMul.hMul stationaryHamiltonian stationaryDensity -
      stationaryDensity*stationaryHamiltonian=0 := by
    rw [stationaryDensity_scalar]
    simp [Matrix.mul_smul,Matrix.smul_mul]
  constructor
  · intro t
    have hK : mixedCoefficient (coordinateDensity hH stationaryDensity)=0 := by
      rw [stationaryDensity_coordinates]
      norm_num [mixedCoefficient,coherence,stationaryDensity]
    have hh := coefficient_hierarchy (coordinateDensity_posSemidef hH stationaryDensity_psd)
      (coordinateDensity_trace hH stationaryDensity_trace)
    have hz : spreadCoefficient (coordinateDensity hH stationaryDensity)
        (coordinateDensity_posSemidef hH stationaryDensity_psd)=0 := by linarith [hh.1,hh.2.1]
    constructor
    · rw [source_spread_eq hH stationaryDensity_psd stationaryDensity_trace,
        spread_eq hH stationaryDensity_psd stationaryDensity_trace,hz,Qubit.threeAtom_zero_parameter]
    · exact commuting_actual_zero _ _ hc t
  · rw [source_purified_eq hH stationaryDensity_psd stationaryDensity_trace,
      purified_eq hH stationaryDensity_psd stationaryDensity_trace,stationaryDensity_coordinates]
    have hp : purifiedCoefficient stationaryDensity=1/2 := by
      norm_num [purifiedCoefficient,stationaryDensity]
    rw [hp,Qubit.threeAtom_half]
    rcases stationaryHamiltonian_gap with hgap | hgap
    · rw [hgap]; norm_num [Real.sin_pi_div_two]
    · rw [hgap]
      simp only [neg_one_mul,neg_div,Real.sin_neg,Real.sin_pi_div_two]
      norm_num


/-- The exact displayed eq:qubit-mus in the literal source GS API. Here p₁,p₂
are the actual density eigenvalues supplied by its diagonalization in the
energy basis, and θ is the polar angle of the actual original-coordinate
energy-to-density eigenbasis transition. Every parameter and coefficient
in the displayed formula is expanded in this single theorem. -/
theorem literal_qubit_formulas {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (t : ℝ) :
    let q := coordinateDensity_posSemidef hH hρ
    let p₁ := q.isHermitian.eigenvalues 0
    let p₂ := q.isHermitian.eigenvalues 1
    let θ := QubitParameterization.polarAngle
      ((energyBasis hH)ᴴ * QubitParameterization.physicalDensityBasis hH hρ)
    let z := (p₁-p₂)^2
    let c := Real.cos θ^2
    PurificationBranches.spread (PurificationBranches.generatorU H)
      (PurificationBranches.seed hρ) t =
      Qubit.threeAtom ((1-Real.sqrt (1-z))*(1-c)/2) (energyGap hH*t) ∧
    PhysicalCurvatureNecessary.mixedComplexity H ρ t =
      Qubit.threeAtom (z*(1-c)/(1+z)) (energyGap hH*t) ∧
    PurificationBranches.pureOperator (PurificationBranches.generatorI H)
      (PurificationBranches.seed hρ) t =
      Qubit.threeAtom ((1-z*c)/2) (energyGap hH*t) := by
  dsimp only
  rw [QubitParameterization.physical_basis_transition]
  simpa only [QubitParameterization.contrast,QubitParameterization.angleParameter,
    Qubit.muS,Qubit.muK,Qubit.muI] using QubitSourceAPI.source_formulas hH hρ htr t


lemma root_parameter_eigenvalues {ρ : QubitMatrix} (hρ : ρ.PosSemidef) :
    rootParameter hρ = 2*Real.sqrt (hρ.isHermitian.eigenvalues 0*hρ.isHermitian.eigenvalues 1) := by
  have hd := density_det_root hρ
  rw [QubitParameterization.eigenvalue_det hρ] at hd
  rw [rootParameter,hd,Real.sqrt_sq (psd_determinant_nonnegative hρ.posSemidef_sqrt)]

lemma density_angular_parameters {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    let θ := QubitParameterization.polarAngle (energyBasis hρ.isHermitian)
    let y := 2*Real.sqrt (hρ.isHermitian.eigenvalues 0*hρ.isHermitian.eigenvalues 1)
    let h := Real.sin θ^2
    spreadCoefficient ρ hρ=(1-y)*h/2 ∧
    mixedCoefficient ρ=(1-y^2)*h/(2-y^2) ∧
    y ∈ Set.Icc (0:ℝ) 1 ∧ h ∈ Set.Icc (0:ℝ) 1 := by
  dsimp only
  rw [← root_parameter_eigenvalues hρ]
  have hz := (QubitParameterization.source_parameters_bounds hρ htr).1
  have hy0 := parameter_nonnegative hρ
  have hy2 : rootParameter hρ^2=1-QubitParameterization.contrast hρ := by
    rw [QubitParameterization.rootParameter_eq_sqrt hρ htr]
    exact Real.sq_sqrt (sub_nonneg.mpr hz.2)
  have hz' : QubitParameterization.contrast hρ=1-rootParameter hρ^2 := by linarith
  have hcos : 1-QubitParameterization.angleParameter hρ =
      Real.sin (QubitParameterization.polarAngle (energyBasis hρ.isHermitian))^2 := by
    dsimp [QubitParameterization.angleParameter]
    nlinarith [Real.sin_sq_add_cos_sq (QubitParameterization.polarAngle (energyBasis hρ.isHermitian))]
  obtain ⟨hS,hK,_⟩ := QubitParameterization.physical_coefficients hρ htr
  refine ⟨?_,?_,⟨hy0,by nlinarith [hz.1]⟩,sq_nonneg _,Real.sin_sq_le_one _⟩
  · rw [hS,Qubit.muS,← QubitParameterization.rootParameter_eq_sqrt hρ htr,hcos]
  · rw [hK,Qubit.muK,hcos,hz']
    congr 1
    ring

/-- Literal eq:qubit-range y/h coefficients: y=2√(p₁p₂), h=sin²θ, with
θ taken from the actual energy-to-density basis transition. The equalities
and closed bounds include pure, maximally mixed and commuting endpoints. -/
theorem literal_qubit_range_parameters {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    let q := coordinateDensity_posSemidef hH hρ
    let θ := QubitParameterization.polarAngle
      ((energyBasis hH)ᴴ * QubitParameterization.physicalDensityBasis hH hρ)
    let y := 2*Real.sqrt (q.isHermitian.eigenvalues 0*q.isHermitian.eigenvalues 1)
    let h := Real.sin θ^2
    spreadCoefficient (coordinateDensity hH ρ) q=(1-y)*h/2 ∧
    mixedCoefficient (coordinateDensity hH ρ)=(1-y^2)*h/(2-y^2) ∧
    y ∈ Set.Icc (0:ℝ) 1 ∧ h ∈ Set.Icc (0:ℝ) 1 := by
  dsimp only
  rw [QubitParameterization.physical_basis_transition]
  exact density_angular_parameters _ (coordinateDensity_trace hH htr)

/-- The source's stricter y<1 and h>0 conditions follow from the original
physical nonstationarity hypothesis, rather than being additional assumptions. -/
theorem nonstationary_angular_parameters {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hc : H*ρ-ρ*H ≠ 0) :
    let q := coordinateDensity_posSemidef hH hρ
    let θ := QubitParameterization.polarAngle
      ((energyBasis hH)ᴴ * QubitParameterization.physicalDensityBasis hH hρ)
    let y := 2*Real.sqrt (q.isHermitian.eigenvalues 0*q.isHermitian.eigenvalues 1)
    y ∈ Set.Ico (0:ℝ) 1 ∧ Real.sin θ^2 ∈ Set.Ioc (0:ℝ) 1 := by
  obtain ⟨hS,_,hy,hh⟩ := literal_qubit_range_parameters hH hρ htr
  have hp := (nonstationary_of_commutator_ne hH hρ htr hc).2
  rw [hS] at hp
  dsimp only at *
  refine ⟨⟨hy.1,lt_of_le_of_ne hy.2 ?_⟩,⟨lt_of_le_of_ne hh.1 ?_,hh.2⟩⟩
  · intro he
    rw [he] at hp
    norm_num at hp
  · intro he
    rw [← he] at hp
    norm_num at hp

end
end Krylov.SourceProse
