import Krylov.FamilySourceAPI

/-! Final source-facing family endpoints. Proof arguments only certify the
manuscript parameter domains; each spread is the existing canonical source API.
All estimates and recurrence analysis are transported from v3 unchanged. -/
namespace Krylov.CanonicalFamilySource
open Matrix OperatorBridge
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section

def mainSpread {ε : ℝ} (h : 0 < ε) (h' : ε ≤ 1/4) (t : ℝ) : ℝ :=
  PurificationBranches.spread
    (PurificationBranches.generatorU (hamiltonian TemporalStates.energy))
    (PurificationBranches.seed (ComplexAdmissibility.MainTemporal.state_posDef h h').posSemidef) t

theorem mainSpread_eq {ε : ℝ} (h : 0 < ε) (h' : ε ≤ 1/4) (t : ℝ) :
    mainSpread h h' t = FamilySourceAPI.mainSpread ε t :=
  (FamilySourceAPI.mainSpread_canonical h h' t).symm

def reciprocalSpread {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) (t : ℝ) : ℝ :=
  PurificationBranches.spread
    (PurificationBranches.generatorU (hamiltonian TemporalStates.energy))
    (PurificationBranches.seed (ComplexAdmissibility.ReciprocalTemporal.state_posDef h h').posSemidef) t

theorem reciprocalSpread_eq {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) (t : ℝ) :
    reciprocalSpread h h' t = FamilySourceAPI.reciprocalSpread η t :=
  (FamilySourceAPI.reciprocalSpread_canonical h h' t).symm

def fixedSpread {ε : ℝ} (h : 0 < ε) (h' : ε < 5/18) (t : ℝ) : ℝ :=
  PurificationBranches.spread
    (PurificationBranches.generatorU (hamiltonian FamilyStates.fixedEnergy))
    (PurificationBranches.seed (ComplexAdmissibility.FixedPurity.state_posDef h h').posSemidef) t

theorem fixedSpread_eq {ε : ℝ} (h : 0 < ε) (h' : ε < 5/18) (t : ℝ) :
    fixedSpread h h' t = FamilySourceAPI.fixedSpread ε t :=
  (FamilySourceAPI.fixedSpread_canonical h h' t).symm

def mainRatio {ε : ℝ} (h : 0 < ε) (h' : ε ≤ 1/4) (t : ℝ) : ℝ :=
  mainSpread h h' t / FamilySourceAPI.mainMixed ε t

theorem mainRatio_eq {ε : ℝ} (h : 0 < ε) (h' : ε ≤ 1/4) :
    mainRatio h h' = FamilySourceAPI.mainRatio ε := by
  funext t
  simp only [mainRatio,FamilySourceAPI.mainRatio,mainSpread_eq h h']

def mainContinued {ε : ℝ} (h : 0 < ε) (h' : ε ≤ 1/4) (t : ℝ) : ℝ :=
  if Real.cos t=1 then TemporalRemovable.mainRecurrenceValue ε else mainRatio h h' t

theorem mainContinued_eq {ε : ℝ} (h : 0 < ε) (h' : ε ≤ 1/4) :
    mainContinued h h' = FamilySourceAPI.mainContinued ε := by
  funext t
  simp only [mainContinued,FamilySourceAPI.mainContinued,mainRatio_eq h h']

def reciprocalRatio {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) (t : ℝ) : ℝ :=
  FamilySourceAPI.reciprocalMixed η t / reciprocalSpread h h' t

theorem reciprocalRatio_eq {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) :
    reciprocalRatio h h' = FamilySourceAPI.reciprocalRatio η := by
  funext t
  simp only [reciprocalRatio,FamilySourceAPI.reciprocalRatio,reciprocalSpread_eq h h']

def reciprocalContinued {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) (t : ℝ) : ℝ :=
  if Real.cos t=1 then TemporalRemovable.reciprocalRecurrenceValue η else reciprocalRatio h h' t

theorem reciprocalContinued_eq {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) :
    reciprocalContinued h h' = FamilySourceAPI.reciprocalContinued η := by
  funext t
  simp only [reciprocalContinued,FamilySourceAPI.reciprocalContinued,reciprocalRatio_eq h h']

def reciprocalScaledContinued {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) (t : ℝ) : ℝ :=
  FamilySourceAPI.reciprocalPurity η * reciprocalContinued h h' t

theorem reciprocalScaledContinued_eq {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) :
    reciprocalScaledContinued h h' = FamilySourceAPI.reciprocalScaledContinued η := by
  funext t
  simp only [reciprocalScaledContinued,FamilySourceAPI.reciprocalScaledContinued,
    reciprocalContinued_eq h h']

def fixedContinued {ε : ℝ} (h : 0 < ε) (h' : ε < 5/18) (t : ℝ) : ℝ :=
  if Real.sin (t/2)=0 then 5/(18*ε)
  else fixedSpread h h' t / FamilySourceAPI.fixedMixed ε t

theorem fixedContinued_eq {ε : ℝ} (h : 0 < ε) (h' : ε < 5/18) :
    fixedContinued h h' = FamilySourceAPI.fixedContinuedRatio ε := by
  funext t
  simp only [fixedContinued,FamilySourceAPI.fixedContinuedRatio,fixedSpread_eq h h']

def qutritSpread {m : ℝ} (hm : 4 ≤ m) (t : ℝ) : ℝ :=
  PurificationBranches.spread
    (PurificationBranches.generatorU (hamiltonian FamilyStates.qutritEnergy))
    (PurificationBranches.seed (ComplexAdmissibility.Qutrit.state_posDef hm).posSemidef) t

theorem qutritSpread_eq {m : ℝ} (hm : 4 ≤ m) (t : ℝ) :
    qutritSpread hm t = FamilySourceAPI.qutritSpread m t :=
  (FamilySourceAPI.qutritSpread_canonical hm t).symm

theorem main_continued_cv_lower {ε : ℝ} (h : 0 < ε) (h' : ε ≤ 1/4) :
    289/(132710400*Real.pi*ε)-1 ≤ Temporal.cvSquared (mainContinued h h') := by
  rw [mainContinued_eq h h']
  exact FamilySourceAPI.main_continued_cv_lower h h'

theorem main_continued_finite_witness :
    80 < PhysicalTemporal.coefficientOfVariation
      (mainContinued (ε := 1/10000000000) (by norm_num) (by norm_num)) := by
  rw [mainContinued_eq]
  exact FamilySourceAPI.main_continued_finite_witness

theorem main_continued_cv_unbounded (M : ℝ) :
    ∃ ε : ℝ, ∃ h : 0 < ε, ∃ h' : ε ≤ 1/4,
      (TemporalStates.mainState ε).PosDef ∧ trace (TemporalStates.mainState ε)=1 ∧
      M < PhysicalTemporal.coefficientOfVariation (mainContinued h h') := by
  obtain ⟨ε,h,h',hp,ht,hM⟩ := FamilySourceAPI.main_continued_cv_unbounded M
  refine ⟨ε,h,h',hp,ht,?_⟩
  rwa [mainContinued_eq h h']

/-- The endpoint identification transports every v3 recurrence display and
moment bound; this conjunct records genuine continuation, not null-set equality. -/
theorem main_continued_source_properties {ε : ℝ} (h : 0 < ε) (h' : ε ≤ 1/4) :
    Continuous (mainContinued h h') ∧
    (∀ t, 0 < mainContinued h h' t) ∧
    Function.Periodic (mainContinued h h') (2*Real.pi) ∧
    Temporal.cvSquared (mainContinued h h')=Temporal.cvSquared (mainRatio h h') := by
  rw [mainContinued_eq h h',mainRatio_eq h h']
  exact ⟨FamilySourceAPI.main_continued_continuous h h',
    FamilySourceAPI.main_continued_positive h h',
    FamilySourceAPI.main_continued_periodic h h',
    FamilySourceAPI.main_continued_cv h h'⟩

theorem reciprocal_continued_cv_lower {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) :
    1/(1679616*Real.pi*η^2)-1 ≤ Temporal.cvSquared (reciprocalContinued h h') := by
  rw [reciprocalContinued_eq h h']
  exact FamilySourceAPI.reciprocal_continued_cv_lower h h'

theorem reciprocal_continued_finite_witness :
    40 < PhysicalTemporal.coefficientOfVariation
      (reciprocalContinued (η := 1/100000) (by norm_num) (by norm_num)) := by
  rw [reciprocalContinued_eq]
  exact FamilySourceAPI.reciprocal_continued_finite_witness

theorem reciprocal_continued_cv_unbounded (M : ℝ) :
    ∃ η : ℝ, ∃ h : 0 < η, ∃ h' : η^2 ≤ 1/16,
      (TemporalStates.reciprocalState η).PosDef ∧ trace (TemporalStates.reciprocalState η)=1 ∧
      M < PhysicalTemporal.coefficientOfVariation (reciprocalContinued h h') := by
  obtain ⟨η,h,h',hp,ht,hM⟩ := FamilySourceAPI.reciprocal_continued_cv_unbounded M
  refine ⟨η,h,h',hp,ht,?_⟩
  rwa [reciprocalContinued_eq h h']

/-- The endpoint identification transports every v3 recurrence display and
moment bound; this conjunct records genuine continuation, not null-set equality. -/
theorem reciprocal_continued_source_properties {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) :
    Continuous (reciprocalContinued h h') ∧
    (∀ t, 0 < reciprocalContinued h h' t) ∧
    Function.Periodic (reciprocalContinued h h') (2*Real.pi) ∧
    Temporal.cvSquared (reciprocalContinued h h')=Temporal.cvSquared (reciprocalRatio h h') := by
  rw [reciprocalContinued_eq h h',reciprocalRatio_eq h h']
  exact ⟨FamilySourceAPI.reciprocal_continued_continuous h h',
    FamilySourceAPI.reciprocal_continued_positive h h',
    FamilySourceAPI.reciprocal_continued_periodic h h',
    FamilySourceAPI.reciprocal_continued_cv h h'⟩

theorem reciprocal_scaled_continued_finite_witness :
    40 < PhysicalTemporal.coefficientOfVariation
      (reciprocalScaledContinued (η := 1/100000) (by norm_num) (by norm_num)) := by
  rw [reciprocalScaledContinued_eq]
  exact FamilySourceAPI.reciprocal_scaled_continued_finite_witness

theorem reciprocal_scaled_continued_cv_value {η : ℝ} (h : 0 < η) (h' : η^2 ≤ 1/16) :
    PhysicalTemporal.coefficientOfVariation (reciprocalScaledContinued h h') =
      PhysicalTemporal.coefficientOfVariation (reciprocalContinued h h') := by
  rw [reciprocalScaledContinued_eq h h',reciprocalContinued_eq h h']
  exact FamilySourceAPI.reciprocal_scaled_continued_cv_value h h'

theorem reciprocal_scaled_continued_cv_unbounded (M : ℝ) :
    ∃ η : ℝ, ∃ h : 0 < η, ∃ h' : η^2 ≤ 1/16,
      (TemporalStates.reciprocalState η).PosDef ∧ trace (TemporalStates.reciprocalState η)=1 ∧
      M < PhysicalTemporal.coefficientOfVariation (reciprocalScaledContinued h h') := by
  obtain ⟨η,h,h',hp,ht,hM⟩ := reciprocal_continued_cv_unbounded M
  refine ⟨η,h,h',hp,ht,?_⟩
  rwa [reciprocal_scaled_continued_cv_value h h']

theorem fixed_uniform_bounds {ε : ℝ} (h : 0 < ε) (h' : ε < 5/18) (t : ℝ) :
    (5/(18*ε))*(1-ε/10) ≤ fixedContinued h h' t ∧ fixedContinued h h' t ≤ 5/(18*ε) := by
  rw [fixedContinued_eq h h']
  exact FamilySourceAPI.fixed_uniform_bounds h h' t

theorem fixed_periodMean_bounds {ε : ℝ} (h : 0 < ε) (h' : ε < 5/18) :
    (5/(18*ε))*(1-ε/10) ≤ Temporal.periodMean (fixedContinued h h') ∧
      Temporal.periodMean (fixedContinued h h') ≤ 5/(18*ε) := by
  rw [fixedContinued_eq h h']
  exact FamilySourceAPI.fixed_periodMean_bounds h h'

theorem fixed_periodMean_unbounded (M : ℝ) :
    ∃ ε : ℝ, ∃ h : 0 < ε, ∃ h' : ε < 5/18,
      (FamilyStates.fixedState ε).PosDef ∧ trace (FamilyStates.fixedState ε)=1 ∧
      trace (FamilyStates.fixedState ε*FamilyStates.fixedState ε)=1/2 ∧
      M < Temporal.periodMean (fixedContinued h h') := by
  obtain ⟨ε,h,h',hp,ht,hp',hM⟩ := FamilySourceAPI.fixed_periodMean_unbounded M
  refine ⟨ε,h,h',hp,ht,hp',?_⟩
  rwa [fixedContinued_eq h h']

theorem fixed_uniformly_diverges (M : ℝ) :
    ∃ ε₀>0, ∀ ε : ℝ, ∀ h : 0 < ε, ε < ε₀ → ∀ h' : ε < 5/18,
      (∀ t : ℝ, M < fixedContinued h h' t) ∧
      M < Temporal.periodMean (fixedContinued h h') := by
  obtain ⟨ε₀,hε₀,hM⟩ := FamilySourceAPI.fixed_uniformly_diverges M
  refine ⟨ε₀,hε₀,?_⟩
  intro ε h he₀ h'
  rw [fixedContinued_eq h h']
  exact hM ε h he₀

theorem qutrit_all_time_strict {m t : ℝ} (hm : 4 ≤ m) (ht : Real.sin (t/2) ≠ 0) :
    FamilySourceAPI.qutritMixed m t < qutritSpread hm t := by
  rw [qutritSpread_eq hm]
  exact FamilySourceAPI.qutrit_all_time_strict hm ht

theorem qutrit_no_positive_multiplier :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, ∀ hm : 4 ≤ m,
      c*qutritSpread hm Real.pi ≤ FamilySourceAPI.qutritMixed m Real.pi := by
  rintro ⟨c,hc,h⟩
  apply FamilySourceAPI.qutrit_no_positive_multiplier
  refine ⟨c,hc,?_⟩
  intro m hm
  simpa only [qutritSpread_eq hm] using h m hm

/-- A totalization solely for the atTop limit. Values below the manuscript
range m >= 4 are zero; on that entire range this is the literal canonical ratio. -/
def qutritPeakRatio (m : ℝ) : ℝ :=
  if hm : 4 ≤ m then qutritSpread hm Real.pi / FamilySourceAPI.qutritMixed m Real.pi else 0

theorem qutrit_peak_ratio {m : ℝ} (hm : 4 ≤ m) :
    qutritPeakRatio m = Ratios.qutritPeakRatio (m^2) := by
  rw [qutritPeakRatio,dif_pos hm,qutritSpread_eq hm]
  exact FamilySourceAPI.qutrit_peak_ratio hm

theorem qutrit_asymptotic :
    Filter.Tendsto (fun m : ℝ => qutritPeakRatio m/m^2)
      Filter.atTop (nhds (1/9 : ℝ)) := by
  apply FamilySourceAPI.qutrit_asymptotic.congr'
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ)] with m hm
  rw [qutritPeakRatio,dif_pos hm,qutritSpread_eq hm]

end
end Krylov.CanonicalFamilySource
