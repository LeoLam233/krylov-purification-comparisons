import Krylov.CertifiedFamilyGS
import Krylov.CertifiedThreeAtomGS
import Krylov.ComplexAdmissibility
import Krylov.TemporalRemovable
import Krylov.FixedPurityCompletion

/-! Source-API consequences for the four parameter families. All spread and
mixed functions below are defined directly by the existing normalized GS API.
Canonical-root equalities, all-time identifications, removable limits, and
headline inequalities are then transported through checked equalities. -/
namespace Krylov.FamilySourceAPI
open Matrix OperatorBridge
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option maxHeartbeats 1000000

lemma trace_complexify {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    trace (A.map Complex.ofReal)=((trace A : ℝ) : ℂ) := by
  simp [Matrix.trace,Matrix.map_apply]

/-- Literal normalized Gram--Schmidt spread for the main family. -/
def mainSpread (ε t : ℝ) : ℝ :=
  PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian (hamiltonian TemporalStates.energy))
    (PhysicalCurvatureNecessary.normalizedSeed ((TemporalStates.mainRoot ε).map Complex.ofReal)) t

/-- Literal mixed-density source API for the main family. -/
def mainMixed (ε t : ℝ) : ℝ :=
  PhysicalCurvatureNecessary.mixedComplexity (hamiltonian TemporalStates.energy)
    ((TemporalStates.mainState ε).map Complex.ofReal) t

theorem mainSpread_eq {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (t : ℝ) :
    mainSpread ε t=FiveAtomFamilies.mainSpread ε t :=
  CertifiedFamilyGS.five_atom (FiveAtomFamilies.mainRoot_data he he') t

theorem mainMixed_eq {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (t : ℝ) :
    mainMixed ε t=FiveAtomFamilies.mainMixed ε t :=
  CertifiedFamilyGS.five_atom (FiveAtomFamilies.mainState_data he he') t

/-- The explicit root in the globally parameterized function is exactly the
canonical positive square root used by the source purification definition. -/
theorem mainSpread_canonical {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (t : ℝ) :
    mainSpread ε t = PurificationBranches.spread
      (PurificationBranches.generatorU (hamiltonian TemporalStates.energy))
      (PurificationBranches.seed (ComplexAdmissibility.MainTemporal.state_posDef he he').posSemidef) t := by
  rw [MatrixGSBridge.spread_eq_normalized (MatrixGSBridge.diagonal_hermitian TemporalStates.energy)
    (ComplexAdmissibility.MainTemporal.state_posDef he he').posSemidef]
  · unfold mainSpread
    rw [ComplexAdmissibility.MainTemporal.root_canonical he he']
  · rw [trace_complexify,TemporalStates.mainState_trace]
    rfl

/-- Literal normalized Gram--Schmidt spread for the reciprocal family. -/
def reciprocalSpread (η t : ℝ) : ℝ :=
  PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian (hamiltonian TemporalStates.energy))
    (PhysicalCurvatureNecessary.normalizedSeed ((TemporalStates.reciprocalRoot η).map Complex.ofReal)) t

/-- Literal mixed-density source API for the reciprocal family. -/
def reciprocalMixed (η t : ℝ) : ℝ :=
  PhysicalCurvatureNecessary.mixedComplexity (hamiltonian TemporalStates.energy)
    ((TemporalStates.reciprocalState η).map Complex.ofReal) t

theorem reciprocalSpread_eq {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) (t : ℝ) :
    reciprocalSpread η t=FiveAtomFamilies.reciprocalSpread η t :=
  CertifiedFamilyGS.five_atom (FiveAtomFamilies.reciprocalRoot_data he he') t

theorem reciprocalMixed_eq {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) (t : ℝ) :
    reciprocalMixed η t=FiveAtomFamilies.reciprocalMixed η t :=
  CertifiedFamilyGS.five_atom (FiveAtomFamilies.reciprocalState_data he he') t

/-- The explicit root in the globally parameterized function is exactly the
canonical positive square root used by the source purification definition. -/
theorem reciprocalSpread_canonical {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) (t : ℝ) :
    reciprocalSpread η t = PurificationBranches.spread
      (PurificationBranches.generatorU (hamiltonian TemporalStates.energy))
      (PurificationBranches.seed (ComplexAdmissibility.ReciprocalTemporal.state_posDef he he').posSemidef) t := by
  rw [MatrixGSBridge.spread_eq_normalized (MatrixGSBridge.diagonal_hermitian TemporalStates.energy)
    (ComplexAdmissibility.ReciprocalTemporal.state_posDef he he').posSemidef]
  · unfold reciprocalSpread
    rw [ComplexAdmissibility.ReciprocalTemporal.root_canonical he he']
  · rw [trace_complexify,TemporalStates.reciprocalState_trace]
    rfl

/-- Literal normalized Gram--Schmidt spread for the fixed family. -/
def fixedSpread (ε t : ℝ) : ℝ :=
  PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian (hamiltonian FamilyStates.fixedEnergy))
    (PhysicalCurvatureNecessary.normalizedSeed ((FamilyStates.fixedRoot ε).map Complex.ofReal)) t

/-- Literal mixed-density source API for the fixed family. -/
def fixedMixed (ε t : ℝ) : ℝ :=
  PhysicalCurvatureNecessary.mixedComplexity (hamiltonian FamilyStates.fixedEnergy)
    ((FamilyStates.fixedState ε).map Complex.ofReal) t

theorem fixedSpread_eq {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) (t : ℝ) :
    fixedSpread ε t=ThreeAtomOperator.fixedSpread ε t :=
  CertifiedFamilyGS.three_atom (ThreeAtomOperator.fixedRoot_data he he') t

theorem fixedMixed_eq {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) (t : ℝ) :
    fixedMixed ε t=ThreeAtomOperator.fixedMixed ε t :=
  CertifiedFamilyGS.three_atom (ThreeAtomOperator.fixedState_data he he') t

/-- The explicit root in the globally parameterized function is exactly the
canonical positive square root used by the source purification definition. -/
theorem fixedSpread_canonical {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) (t : ℝ) :
    fixedSpread ε t = PurificationBranches.spread
      (PurificationBranches.generatorU (hamiltonian FamilyStates.fixedEnergy))
      (PurificationBranches.seed (ComplexAdmissibility.FixedPurity.state_posDef he he').posSemidef) t := by
  rw [MatrixGSBridge.spread_eq_normalized (MatrixGSBridge.diagonal_hermitian FamilyStates.fixedEnergy)
    (ComplexAdmissibility.FixedPurity.state_posDef he he').posSemidef]
  · unfold fixedSpread
    rw [ComplexAdmissibility.FixedPurity.root_canonical he he']
  · rw [trace_complexify,FamilyStates.fixedState_trace]
    rfl

/-- Literal normalized Gram--Schmidt spread for the qutrit family. -/
def qutritSpread (m t : ℝ) : ℝ :=
  PerturbedDynamics.actualComplexity (PerturbedDynamics.liouvillian (hamiltonian FamilyStates.qutritEnergy))
    (PhysicalCurvatureNecessary.normalizedSeed ((FamilyStates.qutritRoot m).map Complex.ofReal)) t

/-- Literal mixed-density source API for the qutrit family. -/
def qutritMixed (m t : ℝ) : ℝ :=
  PhysicalCurvatureNecessary.mixedComplexity (hamiltonian FamilyStates.qutritEnergy)
    ((FamilyStates.qutritState m).map Complex.ofReal) t

theorem qutritSpread_eq {m : ℝ} (hm : 4 ≤ m) (t : ℝ) :
    qutritSpread m t=ThreeAtomOperator.qutritSpread m t :=
  CertifiedFamilyGS.three_atom (ThreeAtomOperator.qutritRoot_data hm) t

theorem qutritMixed_eq {m : ℝ} (hm : 4 ≤ m) (t : ℝ) :
    qutritMixed m t=ThreeAtomOperator.qutritMixed m t :=
  CertifiedFamilyGS.three_atom (ThreeAtomOperator.qutritState_data hm) t

/-- The explicit root in the globally parameterized function is exactly the
canonical positive square root used by the source purification definition. -/
theorem qutritSpread_canonical {m : ℝ} (hm : 4 ≤ m) (t : ℝ) :
    qutritSpread m t = PurificationBranches.spread
      (PurificationBranches.generatorU (hamiltonian FamilyStates.qutritEnergy))
      (PurificationBranches.seed (ComplexAdmissibility.Qutrit.state_posDef hm).posSemidef) t := by
  rw [MatrixGSBridge.spread_eq_normalized (MatrixGSBridge.diagonal_hermitian FamilyStates.qutritEnergy)
    (ComplexAdmissibility.Qutrit.state_posDef hm).posSemidef]
  · unfold qutritSpread
    rw [ComplexAdmissibility.Qutrit.root_canonical hm]
  · rw [trace_complexify,FamilyStates.qutritState_trace]
    rfl

def mainRatio (ε t : ℝ) : ℝ := mainSpread ε t/mainMixed ε t
def reciprocalRatio (η t : ℝ) : ℝ := reciprocalMixed η t/reciprocalSpread η t

theorem mainRatio_eq {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    mainRatio ε=PhysicalTemporal.mainRatio ε := by
  funext t
  simp only [mainRatio,PhysicalTemporal.mainRatio,mainSpread_eq he he',mainMixed_eq he he']

theorem reciprocalRatio_eq {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    reciprocalRatio η=PhysicalTemporal.reciprocalRatio η := by
  funext t
  simp only [reciprocalRatio,PhysicalTemporal.reciprocalRatio,
    reciprocalSpread_eq he he',reciprocalMixed_eq he he']

/-! Temporal coefficient-of-variation theorems in the source GS API. -/
theorem main_cv_lower {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    289/(132710400*Real.pi*ε)-1 ≤ Temporal.cvSquared (mainRatio ε) := by
  rw [mainRatio_eq he he']
  exact PhysicalTemporal.main_cv_lower he he'

theorem reciprocal_cv_lower {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    1/(1679616*Real.pi*η^2)-1 ≤ Temporal.cvSquared (reciprocalRatio η) := by
  rw [reciprocalRatio_eq he he']
  exact PhysicalTemporal.reciprocal_cv_lower he he'

theorem main_cvSquared_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧ (TemporalStates.mainState ε).PosDef ∧
      trace (TemporalStates.mainState ε)=1 ∧ M < Temporal.cvSquared (mainRatio ε) := by
  obtain ⟨ε,he,he',hp,ht,h⟩ := PhysicalTemporal.main_cvSquared_unbounded M
  refine ⟨ε,he,he',hp,ht,?_⟩
  rwa [mainRatio_eq he he']

theorem reciprocal_cvSquared_unbounded (M : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η^2 ≤ 1/16 ∧ (TemporalStates.reciprocalState η).PosDef ∧
      trace (TemporalStates.reciprocalState η)=1 ∧ M < Temporal.cvSquared (reciprocalRatio η) := by
  obtain ⟨η,he,he',hp,ht,h⟩ := PhysicalTemporal.reciprocal_cvSquared_unbounded M
  refine ⟨η,he,he',hp,ht,?_⟩
  rwa [reciprocalRatio_eq he he']

theorem main_cv_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧ (TemporalStates.mainState ε).PosDef ∧
      trace (TemporalStates.mainState ε)=1 ∧
      M < PhysicalTemporal.coefficientOfVariation (mainRatio ε) := by
  obtain ⟨ε,he,he',hp,ht,h⟩ := PhysicalTemporal.main_cv_unbounded M
  refine ⟨ε,he,he',hp,ht,?_⟩
  rwa [mainRatio_eq he he']

theorem reciprocal_cv_unbounded (M : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η^2 ≤ 1/16 ∧ (TemporalStates.reciprocalState η).PosDef ∧
      trace (TemporalStates.reciprocalState η)=1 ∧
      M < PhysicalTemporal.coefficientOfVariation (reciprocalRatio η) := by
  obtain ⟨η,he,he',hp,ht,h⟩ := PhysicalTemporal.reciprocal_cv_unbounded M
  refine ⟨η,he,he',hp,ht,?_⟩
  rwa [reciprocalRatio_eq he he']

theorem main_finite_witness :
    80 < PhysicalTemporal.coefficientOfVariation (mainRatio (1/10000000000)) := by
  rw [mainRatio_eq (by norm_num) (by norm_num)]
  exact PhysicalTemporal.main_finite_witness

theorem reciprocal_finite_witness :
    40 < PhysicalTemporal.coefficientOfVariation (reciprocalRatio (1/100000)) := by
  rw [reciprocalRatio_eq (by norm_num) (by norm_num)]
  exact PhysicalTemporal.reciprocal_finite_witness

theorem purity_rescaled_cv_eq (η : ℝ) :
    PhysicalTemporal.coefficientOfVariation
      (fun t => PhysicalTemporal.reciprocalPurity η*reciprocalRatio η t) =
      PhysicalTemporal.coefficientOfVariation (reciprocalRatio η) := by
  unfold PhysicalTemporal.coefficientOfVariation
  rw [Temporal.cvSquared_scale _ (ne_of_gt (PhysicalTemporal.reciprocalPurity_pos η))]

/-! Explicit source zero sets, continuous extensions, and recurrence limits. -/
theorem mainSpread_zero_iff {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (t : ℝ) :
    mainSpread ε t=0 ↔ Real.cos t=1 := by
  rw [mainSpread_eq he he']
  exact FiveAtomRemovable.complexity_zero_iff (FiveAtomFamilies.mainRoot_data he he') t

theorem mainMixed_zero_iff {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (t : ℝ) :
    mainMixed ε t=0 ↔ Real.cos t=1 := by
  rw [mainMixed_eq he he']
  exact FiveAtomRemovable.complexity_zero_iff (FiveAtomFamilies.mainState_data he he') t

def mainContinued (ε t : ℝ) : ℝ :=
  if Real.cos t=1 then TemporalRemovable.mainRecurrenceValue ε else mainRatio ε t

theorem mainContinued_eq {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    mainContinued ε=TemporalRemovable.mainContinued ε := by
  funext t
  rw [mainContinued,mainRatio_eq he he']
  exact (TemporalRemovable.main_continued_piecewise he he' t).symm

theorem main_continued_continuous {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    Continuous (mainContinued ε) := by
  rw [mainContinued_eq he he']
  exact TemporalRemovable.main_continuous he he'

theorem main_continued_positive {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (t : ℝ) :
    0 < mainContinued ε t := by
  rw [mainContinued_eq he he']
  exact TemporalRemovable.main_positive he he' t

theorem main_continued_cv {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    Temporal.cvSquared (mainContinued ε)=Temporal.cvSquared (mainRatio ε) := by
  rw [mainContinued_eq he he',mainRatio_eq he he']
  exact TemporalRemovable.main_cv_preserved he he'

theorem main_removable_limit {ε t₀ : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4)
    (ht : Real.cos t₀=1) :
    Filter.Tendsto (mainRatio ε) (nhdsWithin t₀ ({t₀}ᶜ))
      (nhds (TemporalRemovable.mainRecurrenceValue ε)) ∧
      0 < TemporalRemovable.mainRecurrenceValue ε := by
  rw [mainRatio_eq he he']
  exact TemporalRemovable.main_removable_limit he he' ht

theorem main_limit_at_every_period {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (n : ℤ) :
    Filter.Tendsto (mainRatio ε)
      (nhdsWithin ((n : ℝ)*(2*Real.pi)) ({(n : ℝ)*(2*Real.pi)}ᶜ))
      (nhds (TemporalRemovable.mainRecurrenceValue ε)) ∧
      0 < TemporalRemovable.mainRecurrenceValue ε := by
  rw [mainRatio_eq he he']
  exact TemporalRemovable.main_limit_at_every_period he he' n

theorem reciprocalSpread_zero_iff {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) (t : ℝ) :
    reciprocalSpread η t=0 ↔ Real.cos t=1 := by
  rw [reciprocalSpread_eq he he']
  exact FiveAtomRemovable.complexity_zero_iff (FiveAtomFamilies.reciprocalRoot_data he he') t

theorem reciprocalMixed_zero_iff {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) (t : ℝ) :
    reciprocalMixed η t=0 ↔ Real.cos t=1 := by
  rw [reciprocalMixed_eq he he']
  exact FiveAtomRemovable.complexity_zero_iff (FiveAtomFamilies.reciprocalState_data he he') t

def reciprocalContinued (η t : ℝ) : ℝ :=
  if Real.cos t=1 then TemporalRemovable.reciprocalRecurrenceValue η else reciprocalRatio η t

theorem reciprocalContinued_eq {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    reciprocalContinued η=TemporalRemovable.reciprocalContinued η := by
  funext t
  rw [reciprocalContinued,reciprocalRatio_eq he he']
  exact (TemporalRemovable.reciprocal_continued_piecewise he he' t).symm

theorem reciprocal_continued_continuous {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    Continuous (reciprocalContinued η) := by
  rw [reciprocalContinued_eq he he']
  exact TemporalRemovable.reciprocal_continuous he he'

theorem reciprocal_continued_positive {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) (t : ℝ) :
    0 < reciprocalContinued η t := by
  rw [reciprocalContinued_eq he he']
  exact TemporalRemovable.reciprocal_positive he he' t

theorem reciprocal_continued_cv {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    Temporal.cvSquared (reciprocalContinued η)=Temporal.cvSquared (reciprocalRatio η) := by
  rw [reciprocalContinued_eq he he',reciprocalRatio_eq he he']
  exact TemporalRemovable.reciprocal_cv_preserved he he'

theorem reciprocal_removable_limit {η t₀ : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16)
    (ht : Real.cos t₀=1) :
    Filter.Tendsto (reciprocalRatio η) (nhdsWithin t₀ ({t₀}ᶜ))
      (nhds (TemporalRemovable.reciprocalRecurrenceValue η)) ∧
      0 < TemporalRemovable.reciprocalRecurrenceValue η := by
  rw [reciprocalRatio_eq he he']
  exact TemporalRemovable.reciprocal_removable_limit he he' ht

theorem reciprocal_limit_at_every_period {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) (n : ℤ) :
    Filter.Tendsto (reciprocalRatio η)
      (nhdsWithin ((n : ℝ)*(2*Real.pi)) ({(n : ℝ)*(2*Real.pi)}ᶜ))
      (nhds (TemporalRemovable.reciprocalRecurrenceValue η)) ∧
      0 < TemporalRemovable.reciprocalRecurrenceValue η := by
  rw [reciprocalRatio_eq he he']
  exact TemporalRemovable.reciprocal_limit_at_every_period he he' n

/-! Fixed-purity uniform separation in the same GS API. -/
def fixedContinuedRatio (ε t : ℝ) : ℝ :=
  if Real.sin (t/2)=0 then 5/(18*ε) else fixedSpread ε t/fixedMixed ε t

theorem fixedContinuedRatio_eq {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) :
    fixedContinuedRatio ε=PhysicalRatios.fixedContinuedRatio ε := by
  funext t
  simp only [fixedContinuedRatio,PhysicalRatios.fixedContinuedRatio,
    fixedSpread_eq he he',fixedMixed_eq he he']

theorem fixed_quotient {ε t : ℝ} (he : 0 < ε) (he' : ε < 5/18)
    (ht : Real.sin (t/2) ≠ 0) :
    fixedSpread ε t/fixedMixed ε t=Ratios.fixedPurityRatio ε (Real.sin (t/2)^2) := by
  rw [fixedSpread_eq he he',fixedMixed_eq he he']
  exact ThreeAtomOperator.fixed_operator_quotient he he' ht

theorem fixed_continued_continuous {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) :
    Continuous (fixedContinuedRatio ε) := by
  rw [fixedContinuedRatio_eq he he']
  exact PhysicalRatios.fixedContinuedRatio_continuous he he'

theorem fixed_uniform_bounds {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) (t : ℝ) :
    (5/(18*ε))*(1-ε/10) ≤ fixedContinuedRatio ε t ∧
      fixedContinuedRatio ε t ≤ 5/(18*ε) := by
  rw [fixedContinuedRatio_eq he he']
  exact PhysicalRatios.fixed_physical_uniform_bounds he he' t

theorem fixed_periodMean_bounds {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) :
    (5/(18*ε))*(1-ε/10) ≤ Temporal.periodMean (fixedContinuedRatio ε) ∧
      Temporal.periodMean (fixedContinuedRatio ε) ≤ 5/(18*ε) := by
  rw [fixedContinuedRatio_eq he he']
  exact PhysicalRatios.fixed_physical_periodMean_bounds he he'

theorem fixed_periodMean_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 5/18 ∧ (FamilyStates.fixedState ε).PosDef ∧
      trace (FamilyStates.fixedState ε)=1 ∧
      trace (FamilyStates.fixedState ε*FamilyStates.fixedState ε)=1/2 ∧
      M < Temporal.periodMean (fixedContinuedRatio ε) := by
  obtain ⟨ε,he,he',hp,ht,hp',h⟩ := PhysicalRatios.fixed_physical_periodMean_unbounded M
  refine ⟨ε,he,he',hp,ht,hp',?_⟩
  rwa [fixedContinuedRatio_eq he he']

theorem fixed_uniformly_diverges (M : ℝ) :
    ∃ ε₀>0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ t : ℝ, M < fixedContinuedRatio ε t) ∧
      M < Temporal.periodMean (fixedContinuedRatio ε) := by
  obtain ⟨ε₀,hε₀,h⟩ := FixedPurityCompletion.uniformly_diverges M
  refine ⟨min ε₀ (5/18),lt_min hε₀ (by norm_num),?_⟩
  intro ε he he₀
  have he' : ε < 5/18 := lt_of_lt_of_le he₀ (min_le_right _ _)
  rw [fixedContinuedRatio_eq he he']
  exact h ε he (lt_of_lt_of_le he₀ (min_le_left _ _))

theorem fixed_reciprocal_uniform_small {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀>0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < 5/18 →
      ∀ t : ℝ, 0 < (1/2)/fixedContinuedRatio ε t ∧
        (1/2)/fixedContinuedRatio ε t < δ := by
  obtain ⟨ε₀,hε₀,h⟩ := FixedPurityCompletion.purity_reciprocal_uniform_small hδ
  refine ⟨ε₀,hε₀,?_⟩
  intro ε he he₀ he' t
  rw [fixedContinuedRatio_eq he he']
  exact h ε he he₀ he' t

/-! The qutrit strict hierarchy and asymptotic/no-multiplier consequences. -/
theorem qutrit_all_time_strict {m t : ℝ} (hm : 4 ≤ m) (ht : Real.sin (t/2) ≠ 0) :
    qutritMixed m t < qutritSpread m t := by
  rw [qutritMixed_eq hm,qutritSpread_eq hm]
  exact PhysicalRatios.qutrit_all_time_strict hm ht

theorem qutrit_peak_ratio {m : ℝ} (hm : 4 ≤ m) :
    qutritSpread m Real.pi/qutritMixed m Real.pi=Ratios.qutritPeakRatio (m^2) := by
  rw [qutritMixed_eq hm,qutritSpread_eq hm]
  exact PhysicalRatios.qutrit_peak_ratio hm

theorem qutrit_asymptotic :
    Filter.Tendsto (fun m : ℝ => (qutritSpread m Real.pi/qutritMixed m Real.pi)/m^2)
      Filter.atTop (nhds (1/9 : ℝ)) := by
  apply PhysicalRatios.qutrit_physical_asymptotic.congr'
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ)] with m hm
  rw [qutritMixed_eq hm,qutritSpread_eq hm]

theorem qutrit_no_positive_multiplier :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, 4 ≤ m →
      c*qutritSpread m Real.pi ≤ qutritMixed m Real.pi := by
  rintro ⟨c,hc,h⟩
  apply ThreeAtomOperator.qutrit_operator_no_positive_multiplier
  refine ⟨c,hc,?_⟩
  intro m hm
  simpa only [qutritMixed_eq hm,qutritSpread_eq hm] using h m hm

/-! Purity factors and reciprocal extensions also refer to the same source
matrices and literal GS ratios. -/
def mainPurity (ε : ℝ) : ℝ :=
  PhysicalCurvatureNecessary.purity ((TemporalStates.mainState ε).map Complex.ofReal)
def reciprocalPurity (η : ℝ) : ℝ :=
  PhysicalCurvatureNecessary.purity ((TemporalStates.reciprocalState η).map Complex.ofReal)

theorem mainPurity_eq (ε : ℝ) : mainPurity ε=TemporalRemovable.mainPurity ε := by
  unfold mainPurity PhysicalCurvatureNecessary.purity TemporalRemovable.mainPurity
  rw [← UnitaryCovariance.complexify_mul,trace_complexify]
  rfl

theorem reciprocalPurity_eq (η : ℝ) : reciprocalPurity η=PhysicalTemporal.reciprocalPurity η := by
  unfold reciprocalPurity PhysicalCurvatureNecessary.purity PhysicalTemporal.reciprocalPurity
  rw [← UnitaryCovariance.complexify_mul,trace_complexify]
  rfl

theorem fixed_purity {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) :
    PhysicalCurvatureNecessary.purity ((FamilyStates.fixedState ε).map Complex.ofReal)=1/2 := by
  unfold PhysicalCurvatureNecessary.purity
  rw [← UnitaryCovariance.complexify_mul,trace_complexify,FamilyStates.fixedState_purity he he']
  norm_num

def mainReciprocalContinued (ε t : ℝ) : ℝ := 1/mainContinued ε t
def mainScaledReciprocalContinued (ε t : ℝ) : ℝ := mainPurity ε*mainReciprocalContinued ε t
def reciprocalScaledContinued (η t : ℝ) : ℝ := reciprocalPurity η*reciprocalContinued η t

theorem mainReciprocalContinued_eq {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    mainReciprocalContinued ε=TemporalRemovable.mainReciprocalContinued ε := by
  funext t
  simp only [mainReciprocalContinued,TemporalRemovable.mainReciprocalContinued,mainContinued_eq he he']

theorem mainScaledReciprocalContinued_eq {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    mainScaledReciprocalContinued ε=TemporalRemovable.mainScaledReciprocalContinued ε := by
  funext t
  simp only [mainScaledReciprocalContinued,TemporalRemovable.mainScaledReciprocalContinued,
    mainPurity_eq,mainReciprocalContinued_eq he he']

theorem reciprocalScaledContinued_eq {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    reciprocalScaledContinued η=TemporalRemovable.reciprocalScaledContinued η := by
  funext t
  simp only [reciprocalScaledContinued,TemporalRemovable.reciprocalScaledContinued,
    reciprocalPurity_eq,reciprocalContinued_eq he he']

theorem main_reciprocal_agrees {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (ht : Real.cos t ≠ 1) :
    mainMixed ε t/mainSpread ε t=mainReciprocalContinued ε t := by
  rw [mainMixed_eq he he',mainSpread_eq he he',mainReciprocalContinued_eq he he']
  exact TemporalRemovable.main_reciprocal_agrees he he' ht

theorem main_reciprocal_limit {ε t₀ : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (ht : Real.cos t₀=1) :
    Filter.Tendsto (fun t => mainMixed ε t/mainSpread ε t) (nhdsWithin t₀ ({t₀}ᶜ))
      (nhds (1/TemporalRemovable.mainRecurrenceValue ε)) ∧
      0 < 1/TemporalRemovable.mainRecurrenceValue ε := by
  simp_rw [mainMixed_eq he he',mainSpread_eq he he']
  exact TemporalRemovable.main_reciprocal_limit he he' ht

theorem main_scaled_reciprocal_limit {ε t₀ : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4)
    (ht : Real.cos t₀=1) :
    Filter.Tendsto (fun t => mainPurity ε*(mainMixed ε t/mainSpread ε t))
      (nhdsWithin t₀ ({t₀}ᶜ)) (nhds (mainPurity ε*(1/TemporalRemovable.mainRecurrenceValue ε))) ∧
      0 < mainPurity ε*(1/TemporalRemovable.mainRecurrenceValue ε) := by
  simp_rw [mainPurity_eq,mainMixed_eq he he',mainSpread_eq he he']
  exact TemporalRemovable.main_scaled_reciprocal_limit he he' ht

theorem reciprocal_scaled_limit {η t₀ : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16)
    (ht : Real.cos t₀=1) :
    Filter.Tendsto (fun t => reciprocalPurity η*reciprocalRatio η t)
      (nhdsWithin t₀ ({t₀}ᶜ)) (nhds (reciprocalPurity η*TemporalRemovable.reciprocalRecurrenceValue η)) ∧
      0 < reciprocalPurity η*TemporalRemovable.reciprocalRecurrenceValue η := by
  simp_rw [reciprocalPurity_eq,reciprocalRatio_eq he he']
  exact TemporalRemovable.reciprocal_scaled_limit he he' ht

theorem reciprocal_source_purity_cv_eq (η : ℝ) :
    PhysicalTemporal.coefficientOfVariation (fun t => reciprocalPurity η*reciprocalRatio η t)=
      PhysicalTemporal.coefficientOfVariation (reciprocalRatio η) := by
  rw [reciprocalPurity_eq]
  exact purity_rescaled_cv_eq η

theorem reciprocal_scaled_finite_witness :
    40 < PhysicalTemporal.coefficientOfVariation
      (fun t => reciprocalPurity (1/100000)*reciprocalRatio (1/100000) t) := by
  rw [reciprocal_source_purity_cv_eq]
  exact reciprocal_finite_witness

theorem main_reciprocal_continued_cv {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    Temporal.cvSquared (mainReciprocalContinued ε)=
      Temporal.cvSquared (fun t => mainMixed ε t/mainSpread ε t) := by
  simp_rw [mainReciprocalContinued_eq he he',mainMixed_eq he he',mainSpread_eq he he']
  exact TemporalRemovable.main_reciprocal_cv_preserved he he'

theorem reciprocal_scaled_continued_cv {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    Temporal.cvSquared (reciprocalScaledContinued η)=
      Temporal.cvSquared (fun t => reciprocalPurity η*reciprocalRatio η t) := by
  simp_rw [reciprocalScaledContinued_eq he he',reciprocalPurity_eq,reciprocalRatio_eq he he']
  exact TemporalRemovable.reciprocal_scaled_cv_preserved he he'

/-- The fixed-purity continuation is explicitly the source scalar expression
at every time, including every recurrence. -/
theorem fixed_continued_formula {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) (t : ℝ) :
    fixedContinuedRatio ε t=Ratios.fixedPurityRatio ε (Real.sin (t/2)^2) := by
  rw [fixedContinuedRatio_eq he he']
  exact PhysicalRatios.fixedContinuedRatio_eq he he' t

theorem fixed_at_recurrence {ε t : ℝ} (ht : Real.sin (t/2)=0) :
    fixedContinuedRatio ε t=5/(18*ε) := by
  simp [fixedContinuedRatio,ht]

/-- The original source ratio has the prescribed punctured recurrence limit. -/
theorem fixed_removable_limit {ε t₀ : ℝ} (he : 0 < ε) (he' : ε < 5/18)
    (ht : Real.sin (t₀/2)=0) :
    Filter.Tendsto (fun t => fixedSpread ε t/fixedMixed ε t) (nhdsWithin t₀ ({t₀}ᶜ))
      (nhds (5/(18*ε))) := by
  have hc := (fixed_continued_continuous he he').tendsto t₀
  rw [fixed_at_recurrence ht] at hc
  apply hc.mono_left inf_le_left |>.congr'
  filter_upwards [FiveAtomRemovable.eventually_nonrecurrence
    ((ReturnLoss.sin_half_zero_iff_recurrence t₀).mp ht)] with t hneq
  have hsin : Real.sin (t/2) ≠ 0 := by
    intro hh
    exact hneq ((ReturnLoss.sin_half_zero_iff_recurrence t).mp hh)
  simp [fixedContinuedRatio,hsin]

/-- Uniform vanishing of the unscaled source reciprocal q=1/r. -/
theorem fixed_unscaled_reciprocal_uniform_small {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀>0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < 5/18 →
      ∀ t : ℝ, 0 < 1/fixedContinuedRatio ε t ∧ 1/fixedContinuedRatio ε t < δ := by
  obtain ⟨ε₀,hε₀,h⟩ := PhysicalRatios.fixed_physical_reciprocal_uniform_small hδ
  refine ⟨ε₀,hε₀,?_⟩
  intro ε he he₀ he' t
  rw [fixedContinuedRatio_eq he he']
  exact h ε he he₀ he' t

theorem fixed_unscaled_reciprocal_bounds {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) (t : ℝ) :
    0 < 1/fixedContinuedRatio ε t ∧ 1/fixedContinuedRatio ε t ≤ 4*ε := by
  rw [fixedContinuedRatio_eq he he']
  exact PhysicalRatios.fixed_physical_reciprocal_bounds he he' t

/-- Both source temporal extensions are genuinely periodic. -/
theorem main_continued_periodic {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    Function.Periodic (mainContinued ε) (2*Real.pi) := by
  rw [mainContinued_eq he he']
  exact TemporalRemovable.main_periodic ε

theorem reciprocal_continued_periodic {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    Function.Periodic (reciprocalContinued η) (2*Real.pi) := by
  rw [reciprocalContinued_eq he he']
  exact TemporalRemovable.reciprocal_periodic η

/-- At each fixed admissible parameter the first and second source moments
exist as finite real interval integrals, before any parameter limit is taken. -/
theorem main_moments_integrable {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    IntervalIntegrable (mainContinued ε) MeasureTheory.volume 0 (2*Real.pi) ∧
      IntervalIntegrable (fun t => mainContinued ε t^2) MeasureTheory.volume 0 (2*Real.pi) := by
  have hc := main_continued_continuous he he'
  exact ⟨hc.intervalIntegrable _ _,(hc.pow 2).intervalIntegrable _ _⟩

theorem reciprocal_moments_integrable {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    IntervalIntegrable (reciprocalContinued η) MeasureTheory.volume 0 (2*Real.pi) ∧
      IntervalIntegrable (fun t => reciprocalContinued η t^2) MeasureTheory.volume 0 (2*Real.pi) := by
  have hc := reciprocal_continued_continuous he he'
  exact ⟨hc.intervalIntegrable _ _,(hc.pow 2).intervalIntegrable _ _⟩

/-! Final temporal headlines stated directly for the genuine continuous
extensions of the source GS quotients. -/
theorem main_continued_cv_lower {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    289/(132710400*Real.pi*ε)-1 ≤ Temporal.cvSquared (mainContinued ε) := by
  rw [main_continued_cv he he']
  exact main_cv_lower he he'

theorem reciprocal_continued_cv_lower {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    1/(1679616*Real.pi*η^2)-1 ≤ Temporal.cvSquared (reciprocalContinued η) := by
  rw [reciprocal_continued_cv he he']
  exact reciprocal_cv_lower he he'

theorem main_continued_cv_value {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    PhysicalTemporal.coefficientOfVariation (mainContinued ε)=
      PhysicalTemporal.coefficientOfVariation (mainRatio ε) :=
  congrArg Real.sqrt (main_continued_cv he he')

theorem reciprocal_continued_cv_value {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    PhysicalTemporal.coefficientOfVariation (reciprocalContinued η)=
      PhysicalTemporal.coefficientOfVariation (reciprocalRatio η) :=
  congrArg Real.sqrt (reciprocal_continued_cv he he')

theorem main_continued_finite_witness :
    80 < PhysicalTemporal.coefficientOfVariation (mainContinued (1/10000000000)) := by
  rw [main_continued_cv_value (by norm_num) (by norm_num)]
  exact main_finite_witness

theorem reciprocal_continued_finite_witness :
    40 < PhysicalTemporal.coefficientOfVariation (reciprocalContinued (1/100000)) := by
  rw [reciprocal_continued_cv_value (by norm_num) (by norm_num)]
  exact reciprocal_finite_witness

theorem main_continued_cv_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧ (TemporalStates.mainState ε).PosDef ∧
      trace (TemporalStates.mainState ε)=1 ∧
      M < PhysicalTemporal.coefficientOfVariation (mainContinued ε) := by
  obtain ⟨ε,he,he',hp,ht,h⟩ := main_cv_unbounded M
  refine ⟨ε,he,he',hp,ht,?_⟩
  rwa [main_continued_cv_value he he']

theorem reciprocal_continued_cv_unbounded (M : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η^2 ≤ 1/16 ∧ (TemporalStates.reciprocalState η).PosDef ∧
      trace (TemporalStates.reciprocalState η)=1 ∧
      M < PhysicalTemporal.coefficientOfVariation (reciprocalContinued η) := by
  obtain ⟨η,he,he',hp,ht,h⟩ := reciprocal_cv_unbounded M
  refine ⟨η,he,he',hp,ht,?_⟩
  rwa [reciprocal_continued_cv_value he he']

theorem reciprocal_scaled_continued_cv_value {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    PhysicalTemporal.coefficientOfVariation (reciprocalScaledContinued η)=
      PhysicalTemporal.coefficientOfVariation (reciprocalContinued η) := by
  have hp : reciprocalPurity η ≠ 0 := by
    rw [reciprocalPurity_eq]
    exact (PhysicalTemporal.reciprocalPurity_pos η).ne'
  unfold PhysicalTemporal.coefficientOfVariation
  rw [reciprocal_scaled_continued_cv he he',reciprocal_continued_cv he he',
    Temporal.cvSquared_scale _ hp]

theorem reciprocal_scaled_continued_finite_witness :
    40 < PhysicalTemporal.coefficientOfVariation (reciprocalScaledContinued (1/100000)) := by
  rw [reciprocal_scaled_continued_cv_value (by norm_num) (by norm_num)]
  exact reciprocal_continued_finite_witness

end
end Krylov.FamilySourceAPI
