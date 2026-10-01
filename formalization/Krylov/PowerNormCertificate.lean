import Krylov.PerturbedDynamics

namespace Krylov.PowerNormCertificate
open Matrix PerturbedDynamics
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Kernel-checkable high-power Frobenius certificates bound the true Euclidean
operator norm of a Hermitian matrix. -/
theorem norm_le_of_power_frobenius (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (n : ℕ) (R : ℝ) (hR : 0≤R)
    (hc : ∑ i,∑ j,‖(B^(2^n)) i j‖^2 ≤ (R^(2^n))^2) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) B‖ ≤ R := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) B
  have hT : IsSelfAdjoint T := (show IsSelfAdjoint B from hB).map _
  have hp : ‖T^(2^n)‖ = ‖T‖^(2^n) := by
    simpa only [NNReal.coe_pow, coe_nnnorm] using
      congrArg (fun x : NNReal => (x : ℝ)) (hT.nnnorm_pow_two_pow n)
  have hb := norm_toEuclideanCLM_le_frobenius (B^(2^n)) (pow_nonneg hR _) hc
  rw [map_pow] at hb
  change ‖T^(2^n)‖ ≤ R^(2^n) at hb
  rw [hp] at hb
  exact (pow_le_pow_iff_left₀ (norm_nonneg T) hR (by positivity : 2^n ≠ 0)).mp hb
end
end Krylov.PowerNormCertificate
