import Krylov.FactorTwoFinite

namespace Krylov.BasisPhaseInvariant
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

/-- Source framework phase convention: unit complex rescaling of each Lanczos
vector leaves every probability and hence every indexed complexity unchanged. -/
theorem amplitude_norm (b x : E) (z : ℂ) (hz : ‖z‖=1) :
    ‖⟪z • b,x⟫_ℂ‖ = ‖⟪b,x⟫_ℂ‖ := by
  simp [inner_smul_left, norm_mul, hz]

theorem complexity_invariant (b : ι → E) (x : E) (degree : ι → ℕ)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖=1) :
    (∑ i, (degree i : ℝ) * ‖⟪z i • b i,x⟫_ℂ‖^2) =
      ∑ i, (degree i : ℝ) * ‖⟪b i,x⟫_ℂ‖^2 := by
  simp_rw [amplitude_norm _ _ _ (hz _)]
end
end Krylov.BasisPhaseInvariant
