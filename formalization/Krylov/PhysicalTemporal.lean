import Krylov.FiveAtomFamilies

/-!
# Physical temporal CV no-go theorems

These ratios use actual commutator Krylov chains, normalized matrix amplitudes,
and canonical positive-root/density-matrix seeds from the two source families.
All period integrals, peak estimates, matrix admissibility and spectral/chain
identifications are proved in the imported modules. Ratios take Lean's total
quotient value at common recurrences; the countable-set invariance theorem
shows that any finite removable assignments give the same temporal statistics.
-/

noncomputable section
namespace Krylov.PhysicalTemporal
open Matrix
open Krylov.FiveAtomFamilies

/-- The main physical complexity ratio. -/
def mainRatio (ε t : ℝ) : ℝ := mainSpread ε t / mainMixed ε t

/-- The reciprocal physical complexity ratio for the second family. -/
def reciprocalRatio (η t : ℝ) : ℝ := reciprocalMixed η t / reciprocalSpread η t

/-- Coefficient of variation computed from the actual recurrence-period moments. -/
def coefficientOfVariation (f : ℝ → ℝ) : ℝ := Real.sqrt (Temporal.cvSquared f)

theorem main_cv_lower {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1 / 4) :
    289 / (132710400 * Real.pi * ε) - 1 ≤ Temporal.cvSquared (mainRatio ε) := by
  exact ReturnLoss.main_cv_of_loss_bounds he he'
    (continuous_mainSpread ε).measurable (continuous_mainMixed ε).measurable
    (mainSpread_loss_bounds he he') (mainMixed_loss_bounds he he')

theorem reciprocal_cv_lower {η : ℝ} (hη : 0 < η) (hη' : η ^ 2 ≤ 1 / 16) :
    1 / (1679616 * Real.pi * η ^ 2) - 1 ≤ Temporal.cvSquared (reciprocalRatio η) := by
  exact ReturnLoss.reciprocal_cv_of_loss_bounds (sq_pos_of_pos hη) hη'
    (continuous_reciprocalSpread η).measurable (continuous_reciprocalMixed η).measurable
    (reciprocalSpread_loss_bounds hη hη') (reciprocalMixed_loss_bounds hη hη')

/-- No finite bound on the main-ratio CV-squared exists, with full-rank,
normalized four-dimensional physical witnesses at the fixed Hamiltonian. -/
theorem main_cvSquared_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ (TemporalStates.mainState ε).PosDef ∧
      trace (TemporalStates.mainState ε) = 1 ∧ M < Temporal.cvSquared (mainRatio ε) := by
  obtain ⟨ε, he, he', h⟩ := TemporalFamilies.inverse_parameter_unbounded
    (show 0 < (289 : ℝ) / (132710400 * Real.pi) by positivity)
    (by norm_num : (0 : ℝ) < 1 / 4) (fun ε => Temporal.cvSquared (mainRatio ε))
    (fun ε he he' => by simpa only [div_div] using main_cv_lower he he') M
  exact ⟨ε, he, he', TemporalStates.mainState_posDef he he', TemporalStates.mainState_trace ε, h⟩

/-- Reciprocal-ratio CV-squared is unbounded on its own physical family. -/
theorem reciprocal_cvSquared_unbounded (M : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η ^ 2 ≤ 1 / 16 ∧ (TemporalStates.reciprocalState η).PosDef ∧
      trace (TemporalStates.reciprocalState η) = 1 ∧ M < Temporal.cvSquared (reciprocalRatio η) := by
  obtain ⟨ε, he, he', h⟩ := TemporalFamilies.inverse_parameter_unbounded
    (show 0 < (1 : ℝ) / (1679616 * Real.pi) by positivity)
    (by norm_num : (0 : ℝ) < 1 / 16) (fun ε => Temporal.cvSquared (reciprocalRatio (Real.sqrt ε)))
    (fun ε he he' => by
      have hη : 0 < Real.sqrt ε := Real.sqrt_pos.2 he
      have hη2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt (le_of_lt he)
      have hη' : Real.sqrt ε ^ 2 ≤ 1 / 16 := by rwa [hη2]
      simpa only [hη2, div_div] using reciprocal_cv_lower hη hη') M
  have hη : 0 < Real.sqrt ε := Real.sqrt_pos.2 he
  have hη' : Real.sqrt ε ^ 2 ≤ 1 / 16 := by rwa [Real.sq_sqrt (le_of_lt he)]
  exact ⟨Real.sqrt ε, hη, hη', TemporalStates.reciprocalState_posDef hη hη',
    TemporalStates.reciprocalState_trace _, h⟩

/-- Direct quantified statement for the coefficient of variation itself. -/
theorem main_cv_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ (TemporalStates.mainState ε).PosDef ∧
      trace (TemporalStates.mainState ε) = 1 ∧ M < coefficientOfVariation (mainRatio ε) := by
  obtain ⟨ε, he, he', hp, ht, h⟩ := main_cvSquared_unbounded (M ^ 2)
  exact ⟨ε, he, he', hp, ht, Real.lt_sqrt_of_sq_lt h⟩

theorem reciprocal_cv_unbounded (M : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η ^ 2 ≤ 1 / 16 ∧ (TemporalStates.reciprocalState η).PosDef ∧
      trace (TemporalStates.reciprocalState η) = 1 ∧
      M < coefficientOfVariation (reciprocalRatio η) := by
  obtain ⟨η, hη, hη', hp, ht, h⟩ := reciprocal_cvSquared_unbounded (M ^ 2)
  exact ⟨η, hη, hη', hp, ht, Real.lt_sqrt_of_sq_lt h⟩

/-- The explicit rational main-family parameter from the manuscript. -/
theorem main_finite_witness :
    80 < coefficientOfVariation (mainRatio (1 / 10000000000)) := by
  have h := main_cv_lower (by norm_num : (0 : ℝ) < 1 / 10000000000)
    (by norm_num : (1 / 10000000000 : ℝ) ≤ 1 / 4)
  exact Real.lt_sqrt_of_sq_lt (lt_of_lt_of_le Temporal.main_finite_threshold h)

/-- The explicit rational reciprocal-family parameter from the manuscript. -/
theorem reciprocal_finite_witness :
    40 < coefficientOfVariation (reciprocalRatio (1 / 100000)) := by
  have h := reciprocal_cv_lower (by norm_num : (0 : ℝ) < 1 / 100000)
    (by norm_num : (1 / 100000 : ℝ) ^ 2 ≤ 1 / 16)
  have hη : (1 / 100000 : ℝ) ^ 2 = 1 / 10000000000 := by norm_num
  rw [hη] at h
  exact Real.lt_sqrt_of_sq_lt (lt_of_lt_of_le Temporal.reciprocal_finite_threshold h)

def reciprocalPurity (η : ℝ) : ℝ :=
  trace (TemporalStates.reciprocalState η * TemporalStates.reciprocalState η)

theorem reciprocalPurity_pos (η : ℝ) : 0 < reciprocalPurity η := by
  unfold reciprocalPurity
  rw [TemporalStates.reciprocalState_purity]
  exact div_pos (TemporalStates.reciprocalT_pos η)
    (sq_pos_of_pos (TemporalStates.reciprocalN_pos η))

/-- Purity rescaling leaves the actual reciprocal-family CV unchanged. -/
theorem purity_rescaled_cv_eq (η : ℝ) :
    coefficientOfVariation (fun t => reciprocalPurity η * reciprocalRatio η t) =
      coefficientOfVariation (reciprocalRatio η) := by
  unfold coefficientOfVariation
  rw [Temporal.cvSquared_scale _ (ne_of_gt (reciprocalPurity_pos η))]

end Krylov.PhysicalTemporal
