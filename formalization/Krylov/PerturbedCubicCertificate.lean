import Krylov.AncillaNormCertificate
import Krylov.NumberBoundSeven
import Krylov.CubicRemainder

namespace Krylov.PerturbedCubicCertificate
open PerturbedDynamics CubicRemainder
noncomputable section

/-- The manuscript appendix's displayed cubic lower bound, with its exact
constant and every real time. All norm and chain-degree bounds are supplied by
kernel-checked power/annihilator certificates for the actual generators. -/
theorem source_cubic_lower_bound (t : ℝ) :
    (53/3380)*t^2-(21296/125)*|t|^3 ≤ mixedComplexity (1/20) t-purifiedComplexity (1/20) t := by
  have hm := actual_cubic_remainder_11_5_six (liouvillian (complexHamiltonian (1/20)))
    (liouvillian_selfAdjoint _ (complexHamiltonian_hermitian _))
    mixedVector mixedVector_unit (mixedVector_orthogonal _)
    RationalPowerCertificates.L_norm (NumberBoundSeven.mixed_number_six _) t
  have hp := actual_cubic_remainder_11_5_six (liouvillian (purifiedGenerator (1/20)))
    (liouvillian_selfAdjoint _ (purifiedGenerator_hermitian _))
    purifiedVector purifiedVector_unit (purifiedVector_orthogonal _)
    AncillaNormCertificate.purified_liouvillian_sharp_bound (NumberBoundSeven.purified_number_six _) t
  rw [mixed_curvature] at hm
  rw [purified_curvature] at hp
  change |mixedComplexity (1/20) t-Perturbation.mixedCurvature (1/20)*t^2| ≤ _ at hm
  change |purifiedComplexity (1/20) t-Perturbation.purifiedCurvature (1/20)*t^2| ≤ _ at hp
  have hlo := (abs_le.mp hm).1
  have hhi := (abs_le.mp hp).2
  have hk := congrArg (fun x : ℝ => x*t^2) Perturbation.curvature_finite
  nlinarith
end
end Krylov.PerturbedCubicCertificate
