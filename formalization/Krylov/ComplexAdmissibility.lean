import Krylov.UnitaryCovariance
import Krylov.FamilyStates
import Krylov.TemporalStates

/-! Explicit complex-field positivity and canonical square-root transport for
all parameter-family witnesses used by the operator theorems. -/
namespace Krylov.ComplexAdmissibility
open Matrix UnitaryCovariance
open scoped ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexify_canonical_root (A R : Matrix ι ι ℝ) (hA : A.PosDef)
    (hR : R.PosDef) (hs : R*R=A) :
    R.map Complex.ofReal = (complexify_posDef A hA).posSemidef.sqrt := by
  apply (complexify_posDef R hR).posSemidef.eq_sqrt_of_sq_eq
  simpa only [pow_two,← complexify_mul] using congrArg (fun B => B.map Complex.ofReal) hs

namespace Qutrit

theorem state_posDef {m : ℝ} (hm : 4 ≤ m) :
    ((FamilyStates.qutritState m).map Complex.ofReal).PosDef :=
  complexify_posDef _ (FamilyStates.qutritState_posDef hm)

theorem root_canonical {m : ℝ} (hm : 4 ≤ m) :
    (FamilyStates.qutritRoot m).map Complex.ofReal = (state_posDef hm).posSemidef.sqrt :=
  complexify_canonical_root _ _ (FamilyStates.qutritState_posDef hm)
    (FamilyStates.qutritRoot_posDef hm) (FamilyStates.qutritRoot_square m)
end Qutrit

namespace FixedPurity

theorem state_posDef {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) :
    ((FamilyStates.fixedState ε).map Complex.ofReal).PosDef :=
  complexify_posDef _ (FamilyStates.fixedState_posDef he he')

theorem root_canonical {ε : ℝ} (he : 0 < ε) (he' : ε < 5/18) :
    (FamilyStates.fixedRoot ε).map Complex.ofReal = (state_posDef he he').posSemidef.sqrt :=
  complexify_canonical_root _ _ (FamilyStates.fixedState_posDef he he')
    (FamilyStates.fixedRoot_posDef he he') (FamilyStates.fixedRoot_square he he')
end FixedPurity

namespace MainTemporal

theorem state_posDef {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    ((TemporalStates.mainState ε).map Complex.ofReal).PosDef :=
  complexify_posDef _ (TemporalStates.mainState_posDef he he')

theorem root_canonical {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    (TemporalStates.mainRoot ε).map Complex.ofReal = (state_posDef he he').posSemidef.sqrt :=
  complexify_canonical_root _ _ (TemporalStates.mainState_posDef he he')
    (TemporalStates.mainRoot_posDef he he') (TemporalStates.mainRoot_square he he')
end MainTemporal

namespace ReciprocalTemporal

theorem state_posDef {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    ((TemporalStates.reciprocalState η).map Complex.ofReal).PosDef :=
  complexify_posDef _ (TemporalStates.reciprocalState_posDef he he')

theorem root_canonical {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    (TemporalStates.reciprocalRoot η).map Complex.ofReal = (state_posDef he he').posSemidef.sqrt :=
  complexify_canonical_root _ _ (TemporalStates.reciprocalState_posDef he he')
    (TemporalStates.reciprocalRoot_posDef he he') (TemporalStates.reciprocalRoot_square η)
end ReciprocalTemporal

end
end Krylov.ComplexAdmissibility
