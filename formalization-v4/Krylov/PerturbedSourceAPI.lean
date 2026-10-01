import Krylov.RightWitnessCurvature
import Krylov.PerturbedCubicCertificate

/-! Delta-general transport to the manuscript's literal canonical source API.
No new dynamical estimate is introduced here. -/
namespace Krylov.PerturbedSourceAPI
open Matrix PerturbedDynamics
open scoped ComplexOrder
noncomputable section

/-- The fixed density seed is normalized identically for every Hamiltonian. -/
theorem mixed_canonical (δ t : ℝ) :
    PerturbedDynamics.mixedComplexity δ t =
      PhysicalCurvatureNecessary.mixedComplexity (complexHamiltonian δ)
        (States.rhoR.map Complex.ofReal) t := by
  unfold PhysicalCurvatureNecessary.mixedComplexity PerturbedDynamics.mixedComplexity
  rw [show States.rhoR.map Complex.ofReal = mixedSeed from rfl,
    RightWitnessCurvature.mixed_seed_normalized]

/-- The canonical purification projector is independent of delta, while the
I-branch generator is H_delta tensor I for every real delta. -/
theorem purified_canonical (δ t : ℝ) :
    PerturbedDynamics.purifiedComplexity δ t =
      PurificationBranches.pureOperator
        (PurificationBranches.generatorI (complexHamiltonian δ))
        (PurificationBranches.seed UnitaryCovariance.complex_rhoR_posDef.posSemidef) t := by
  symm
  rw [PurificationBranches.pureOperator,← PureShortTime.operatorComplexity_physical _
    (PurificationBranches.generatorI_hermitian (complexHamiltonian_hermitian δ))]
  have hs : FactorTwo.pureSeed
      (PurificationBranches.seed UnitaryCovariance.complex_rhoR_posDef.posSemidef) =
      PurifiedCovariance.originalSeed := by
    have he := UnitaryCovariance.complex_rootR_canonical
    ext ⟨i,j⟩ ⟨k,l⟩
    simp only [FactorTwo.pureSeed,FactorTwo.outer,PurificationBranches.seed,
      PurifiedCovariance.originalSeed,Purification.pureSeed,PurifiedCovariance.originalRoot,
      ← he]
  rw [hs,PurificationBranches.generatorI_eq_kronecker]
  simp only [PerturbedDynamics.purifiedComplexity,purifiedGenerator,
    purifiedVector,PurifiedCovariance.lift]

/-- The robust proposition, including irreducibility, at the canonical source endpoint. -/
theorem robust_qutrit_witness {δ : ℝ} (hδ0 : 0 < |δ|)
    (hδ : |δ| < 1/Real.sqrt 135) :
    (∀ P : Matrix (Fin 3) (Fin 3) ℂ,
      P*P=P → P*(States.rhoR.map Complex.ofReal)=(States.rhoR.map Complex.ofReal)*P →
      P*complexHamiltonian δ=complexHamiltonian δ*P → P=0 ∨ P=1) ∧
    (∃ ε>0, ∀ t : ℝ, 0<t → t<ε →
      PurificationBranches.pureOperator
        (PurificationBranches.generatorI (complexHamiltonian δ))
        (PurificationBranches.seed UnitaryCovariance.complex_rhoR_posDef.posSemidef) t <
      PhysicalCurvatureNecessary.mixedComplexity (complexHamiltonian δ)
        (States.rhoR.map Complex.ofReal) t) := by
  obtain ⟨hirr,ε,hε,h⟩ := PerturbedDynamics.robust_qutrit_witness hδ0 hδ
  refine ⟨hirr,ε,hε,?_⟩
  intro t ht hte
  rw [← purified_canonical,← mixed_canonical]
  exact h t ht hte

/-- The exact finite certificate in literal C_M and canonical K_I. -/
theorem finite_certificate :
    (378247/21125000000000000 : ℝ) ≤
      PhysicalCurvatureNecessary.mixedComplexity (complexHamiltonian (1/20))
        (States.rhoR.map Complex.ofReal) (1/20000) -
      PurificationBranches.pureOperator
        (PurificationBranches.generatorI (complexHamiltonian (1/20)))
        (PurificationBranches.seed UnitaryCovariance.complex_rhoR_posDef.posSemidef) (1/20000) := by
  rw [← purified_canonical,← mixed_canonical]
  exact PerturbedDynamics.perturbed_finite_lower_bound

/-- The printed cubic estimate, at every real time, in canonical source quantities. -/
theorem cubic_certificate (t : ℝ) :
    (53/3380)*t^2-(21296/125)*|t|^3 ≤
      PhysicalCurvatureNecessary.mixedComplexity (complexHamiltonian (1/20))
        (States.rhoR.map Complex.ofReal) t -
      PurificationBranches.pureOperator
        (PurificationBranches.generatorI (complexHamiltonian (1/20)))
        (PurificationBranches.seed UnitaryCovariance.complex_rhoR_posDef.posSemidef) t := by
  rw [← purified_canonical,← mixed_canonical]
  exact PerturbedCubicCertificate.source_cubic_lower_bound t

end
end Krylov.PerturbedSourceAPI
