import Krylov.PurificationBranches
import Krylov.PerturbedDynamics
import Krylov.UniversalQubit

/-!
# The two canonical purification branches and their physical marginals

The literal matrix exponentials of `H⊗I` and `H⊗I−I⊗conj(H)` are related to
left multiplication and unitary conjugation of the actual positive square root.
Both branches' physical partial traces are exactly `UρU†`. No equality between
the physical and ancilla marginals is asserted.
-/

noncomputable section
namespace Krylov.CanonicalPurification
open Matrix PurificationBranches UnitaryEvolution
open scoped BigOperators InnerProductSpace ComplexOrder
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Literal physical partial trace of an operator on the doubled space. -/
def physicalPartialTrace (R : Matrix (ι × ι) (ι × ι) ℂ) : Matrix ι ι ℂ :=
  fun i j => ∑ a, R (i,a) (j,a)

/-- Physical marginal of the actual rank-one vector density matrix. -/
def physicalReduced (ψ : ι × ι → ℂ) : Matrix ι ι ℂ :=
  physicalPartialTrace (FactorTwo.outer ψ ψ)

def row (X : Matrix ι ι ℂ) : ι × ι → ℂ := fun a => X a.1 a.2

theorem physicalReduced_row (X : Matrix ι ι ℂ) : physicalReduced (row X) = X * Xᴴ := by
  ext i j
  simp [physicalReduced, physicalPartialTrace, FactorTwo.outer, row, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

theorem row_hilbert (X : Matrix ι ι ℂ) : hilbertVector (row X) = FactorTwo.rowVectorize X := rfl

theorem generatorI_row (H X : Matrix ι ι ℂ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι × ι)) (generatorI H) (FactorTwo.rowVectorize X) =
      FactorTwo.rowVectorize (H * X) := by
  apply (WithLp.equiv 2 ((ι × ι) → ℂ)).injective
  ext ⟨i,j⟩
  change (∑ b : ι × ι, generatorI H (i,j) b * X b.1 b.2) = (H * X) i j
  simp [generatorI, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, mul_ite]

theorem generatorU_eq_commutatorMatrix {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    generatorU H = PerturbedDynamics.commutatorMatrix H := by
  ext ⟨i,j⟩ ⟨k,l⟩
  have hs : star (H j l) = H l j := congrFun (congrFun hH l) j
  simp only [generatorU, generatorI, Matrix.sub_apply, Matrix.of_apply,
    PerturbedDynamics.commutatorMatrix, hs]

theorem generatorU_row {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (X : Matrix ι ι ℂ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι × ι)) (generatorU H) (FactorTwo.rowVectorize X) =
      FactorTwo.rowVectorize (H * X - X * H) := by
  rw [generatorU_eq_commutatorMatrix hH]
  exact PerturbedDynamics.liouvillian_rowVectorize H X

section MatrixExponential
attribute [local instance] Matrix.linftyOpSemiNormedRing Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Transport of the literal matrix exponential to its Euclidean operator. -/
theorem matrix_exp_action {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℂ) (c : ℂ) (x : EuclideanSpace ℂ κ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ)) (NormedSpace.exp ℂ (c • G)) x =
      NormedSpace.exp ℂ (c • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ)) G) x := by
  let F : Matrix κ κ ℂ →ₗ[ℂ] (EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ) :=
    { toFun := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ)
      map_add' := map_add (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ))
      map_smul' := fun a A => by
        exact map_smul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ)) a A }
  have hmap := NormedSpace.map_exp ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ))
    F.continuous_of_finiteDimensional (c • G)
  rw [hmap, map_smul]

theorem branchI_evolution (H X : Matrix ι ι ℂ) (t : ℝ) :
    evolvedVector (generatorI H) (row X) t = FactorTwo.rowVectorize (propagator H t * X) := by
  let T : Matrix ι ι ℂ →L[ℂ] EuclideanSpace ℂ (ι × ι) :=
    (FactorTwo.rowVectorize (ι := ι)).toContinuousLinearEquiv.toContinuousLinearMap
  let L := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι × ι)) (generatorI H)
  let c : ℂ := -((t : ℂ) * Complex.I)
  have hh := TaylorRemainder.exponential_intertwining T (CyclicEvolution.left H) L
    (fun Y => by simpa [T,L,CyclicEvolution.left_apply] using (generatorI_row H Y).symm) X c
  have hleft : c • CyclicEvolution.left H = CyclicEvolution.left (c • H) := by
    ext Y
    simp [CyclicEvolution.left_apply, smul_mul_assoc]
  rw [hleft, CyclicEvolution.exp_left_apply] at hh
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι × ι))
    (NormedSpace.exp ℂ (c • generatorI H)) (FactorTwo.rowVectorize X) = _
  rw [matrix_exp_action]
  exact hh.symm

theorem branchU_evolution {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (X : Matrix ι ι ℂ) (t : ℝ) :
    evolvedVector (generatorU H) (row X) t =
      FactorTwo.rowVectorize (propagator H t * X * (propagator H t)ᴴ) := by
  let T : Matrix ι ι ℂ →L[ℂ] EuclideanSpace ℂ (ι × ι) :=
    (FactorTwo.rowVectorize (ι := ι)).toContinuousLinearEquiv.toContinuousLinearMap
  let L := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι × ι)) (generatorU H)
  let c : ℂ := -((t : ℂ) * Complex.I)
  have hh := TaylorRemainder.exponential_intertwining T (CyclicEvolution.ad H) L
    (fun Y => by simpa [T,L,CyclicEvolution.ad_apply] using (generatorU_row hH Y).symm) X c
  rw [CyclicEvolution.exp_ad_apply] at hh
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι × ι))
    (NormedSpace.exp ℂ (c • generatorU H)) (FactorTwo.rowVectorize X) = _
  rw [matrix_exp_action]
  change NormedSpace.exp ℂ (c • L) (T X) = _
  rw [← hh]
  change FactorTwo.rowVectorize _ = FactorTwo.rowVectorize _
  apply congrArg FactorTwo.rowVectorize
  unfold propagator
  change NormedSpace.exp ℂ (c • H) * X * NormedSpace.exp ℂ ((-c) • H) =
    NormedSpace.exp ℂ (c • H) * X * (NormedSpace.exp ℂ (c • H))ᴴ
  rw [← Matrix.exp_conjTranspose]
  congr 2
  simp [Matrix.conjTranspose_smul, hH.eq, c, Complex.star_def]

end MatrixExponential

def evolvedDensity (H ρ : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  UnitaryCovariance.changeBasis ((propagator H t)ᴴ) ρ

/-- The density definition is literally the original unitary conjugation. -/
theorem evolvedDensity_eq (H ρ : Matrix ι ι ℂ) (t : ℝ) :
    evolvedDensity H ρ t = propagator H t * ρ * (propagator H t)ᴴ := by
  simp [evolvedDensity, UnitaryCovariance.changeBasis]

theorem evolvedDensity_posSemidef (H : Matrix ι ι ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (t : ℝ) : (evolvedDensity H ρ t).PosSemidef :=
  UniversalQubit.changeBasis_posSemidef ((propagator H t)ᴴ) hρ

theorem evolvedDensity_trace {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ρ : Matrix ι ι ℂ) (t : ℝ) : trace (evolvedDensity H ρ t) = trace ρ := by
  have hh := UniversalQubit.changeBasis_trace ((propagator H t)ᴴ) ρ
    (by simpa using (propagator_unitary H hH t).1)
  simpa only [UnitaryCovariance.changeBasis, Matrix.conjTranspose_conjTranspose,
    evolvedDensity] using hh

/-- Generic covariance of the canonical positive square root, for arbitrary finite dimension. -/
theorem evolved_sqrt {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (t : ℝ) :
    propagator H t * hρ.sqrt * (propagator H t)ᴴ = (evolvedDensity_posSemidef H hρ t).sqrt := by
  have hU := (propagator_unitary H hH t).1
  have hh := UniversalQubit.sqrt_coordinates ((propagator H t)ᴴ) hρ (by simpa using hU)
  simpa only [UnitaryCovariance.changeBasis, Matrix.conjTranspose_conjTranspose,
    evolvedDensity] using hh

/-- Literal U*-branch exponential equals row vectorization of the canonical root of ρ(t). -/
theorem canonical_branchU {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (t : ℝ) :
    evolvedVector (generatorU H) (seed hρ) t =
      FactorTwo.rowVectorize (evolvedDensity_posSemidef H hρ t).sqrt := by
  change evolvedVector (generatorU H) (row hρ.sqrt) t = _
  rw [branchU_evolution hH, evolved_sqrt hH hρ]

/-- Literal I-branch exponential has physical marginal ρ(t). -/
theorem physical_reduced_I {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (t : ℝ) :
    physicalReduced (fun a => evolvedVector (generatorI H) (seed hρ) t a) = evolvedDensity H ρ t := by
  change physicalReduced (fun a => evolvedVector (generatorI H) (row hρ.sqrt) t a) = _
  rw [branchI_evolution]
  change physicalReduced (row (propagator H t * hρ.sqrt)) = _
  rw [physicalReduced_row, Matrix.conjTranspose_mul, hρ.posSemidef_sqrt.isHermitian.eq]
  simp only [evolvedDensity, UnitaryCovariance.changeBasis, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc hρ.sqrt hρ.sqrt, hρ.sqrt_mul_self]

/-- Literal U*-branch exponential has the same physical marginal ρ(t). -/
theorem physical_reduced_U {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (t : ℝ) :
    physicalReduced (fun a => evolvedVector (generatorU H) (seed hρ) t a) = evolvedDensity H ρ t := by
  rw [canonical_branchU hH hρ]
  change physicalReduced (row (evolvedDensity_posSemidef H hρ t).sqrt) = _
  rw [physicalReduced_row, (evolvedDensity_posSemidef H hρ t).posSemidef_sqrt.isHermitian.eq,
    (evolvedDensity_posSemidef H hρ t).sqrt_mul_self]

/-- Both canonical branches realize the required physical evolution. -/
theorem both_physical_reduced_densities {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (t : ℝ) :
    physicalReduced (fun a => evolvedVector (generatorI H) (seed hρ) t a) = evolvedDensity H ρ t ∧
    physicalReduced (fun a => evolvedVector (generatorU H) (seed hρ) t a) = evolvedDensity H ρ t :=
  ⟨physical_reduced_I hH hρ t, physical_reduced_U hH hρ t⟩

/-- For a density matrix, both literal branch evolutions remain unit vectors. -/
theorem canonical_branches_normalized {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) (t : ℝ) :
    ‖evolvedVector (generatorI H) (seed hρ) t‖ = 1 ∧
      ‖evolvedVector (generatorU H) (seed hρ) t‖ = 1 := by
  exact ⟨evolvedVector_unit _ (generatorI_hermitian hH) _ (seed_unit hρ htrace) t,
    evolvedVector_unit _ (generatorU_hermitian hH) _ (seed_unit hρ htrace) t⟩

end Krylov.CanonicalPurification
