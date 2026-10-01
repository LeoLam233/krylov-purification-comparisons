import Krylov.FamilySourceAPI

namespace Krylov.SourceRecurrenceSets
open FamilySourceAPI
noncomputable section

theorem main_zero_sets {ε : ℝ} (he : 0<ε) (he' : ε≤1/4) (t : ℝ) :
    (mainSpread ε t=0 ↔ ∃ n : ℤ, (n:ℝ)*(2*Real.pi)=t) ∧
    (mainMixed ε t=0 ↔ ∃ n : ℤ, (n:ℝ)*(2*Real.pi)=t) :=
  ⟨(mainSpread_zero_iff he he' t).trans (Real.cos_eq_one_iff t),
    (mainMixed_zero_iff he he' t).trans (Real.cos_eq_one_iff t)⟩

theorem reciprocal_zero_sets {η : ℝ} (he : 0<η) (he' : η^2≤1/16) (t : ℝ) :
    (reciprocalSpread η t=0 ↔ ∃ n : ℤ, (n:ℝ)*(2*Real.pi)=t) ∧
    (reciprocalMixed η t=0 ↔ ∃ n : ℤ, (n:ℝ)*(2*Real.pi)=t) :=
  ⟨(reciprocalSpread_zero_iff he he' t).trans (Real.cos_eq_one_iff t),
    (reciprocalMixed_zero_iff he he' t).trans (Real.cos_eq_one_iff t)⟩

theorem main_pi_nonrecurrence {ε : ℝ} (he : 0<ε) (he' : ε≤1/4) :
    mainSpread ε Real.pi ≠ 0 ∧ mainMixed ε Real.pi ≠ 0 := by
  norm_num [mainSpread_zero_iff he he',mainMixed_zero_iff he he']

theorem reciprocal_pi_nonrecurrence {η : ℝ} (he : 0<η) (he' : η^2≤1/16) :
    reciprocalSpread η Real.pi ≠ 0 ∧ reciprocalMixed η Real.pi ≠ 0 := by
  norm_num [reciprocalSpread_zero_iff he he',reciprocalMixed_zero_iff he he']

end
end Krylov.SourceRecurrenceSets
