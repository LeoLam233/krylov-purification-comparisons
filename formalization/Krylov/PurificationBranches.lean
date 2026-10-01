import Krylov.FactorTwoTheorem
import Krylov.UnitaryCovariance
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Krylov.PurificationBranches
open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder Kronecker
set_option linter.unusedSectionVars false
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def generatorI (H : Matrix ι ι ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  fun a b => H a.1 b.1 * if a.2 = b.2 then 1 else 0

def generatorU (H : Matrix ι ι ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  generatorI H - (of fun (a b : ι × ι) => (if a.1 = b.1 then 1 else 0) * star (H a.2 b.2))

/-- Literal source tensor-product notation. -/
theorem generatorI_eq_kronecker (H : Matrix ι ι ℂ) :
    generatorI H = H ⊗ₖ (1 : Matrix ι ι ℂ) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [generatorI, kronecker_apply, Matrix.one_apply]

theorem generatorU_eq_kronecker (H : Matrix ι ι ℂ) :
    generatorU H = H ⊗ₖ (1 : Matrix ι ι ℂ) -
      (1 : Matrix ι ι ℂ) ⊗ₖ H.map star := by
  rw [← generatorI_eq_kronecker]
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [generatorU, kronecker_apply, Matrix.one_apply]

theorem generatorI_hermitian {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    (generatorI H).IsHermitian := by
  ext a b
  have h := congrFun (congrFun hH a.1) b.1
  simp only [conjTranspose_apply] at h ⊢
  by_cases hab : a.2 = b.2 <;> simp [generatorI, hab, eq_comm, h]

theorem generatorU_hermitian {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    (generatorU H).IsHermitian := by
  unfold generatorU
  apply (generatorI_hermitian hH).sub
  ext a b
  have h := congrFun (congrFun hH a.2) b.2
  simp only [conjTranspose_apply] at h ⊢
  by_cases hab : a.1 = b.1 <;> simp [hab, eq_comm, ← h]

def seed {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) : ι × ι → ℂ :=
  fun a => hρ.sqrt a.1 a.2

theorem seed_unit {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    ‖UnitaryEvolution.hilbertVector (seed hρ)‖ = 1 := by
  have hi : ⟪UnitaryEvolution.hilbertVector (seed hρ),
      UnitaryEvolution.hilbertVector (seed hρ)⟫_ℂ = 1 := by
    change ⟪FactorTwo.rowVectorize hρ.sqrt, FactorTwo.rowVectorize hρ.sqrt⟫_ℂ = 1
    rw [FactorTwo.rowVectorize_inner]
    change OperatorBridge.hsInner hρ.sqrt hρ.sqrt = 1
    rw [UnitaryCovariance.hsInner_eq_trace, hρ.posSemidef_sqrt.isHermitian,
      hρ.sqrt_mul_self, htrace]
  have hn : ‖UnitaryEvolution.hilbertVector (seed hρ)‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, hi]
    rfl
  nlinarith [norm_nonneg (UnitaryEvolution.hilbertVector (seed hρ))]

/-- Source cor:branches, with both concrete purification generators and the
canonical normalized seed; valid also for rank-deficient densities. -/
theorem both_branches {H ρ : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) (t : ℝ) :
    (2 * FactorTwoFinite.complexity (FactorTwoFinite.stateSequence (generatorI H) (seed hρ))
      (UnitaryEvolution.evolvedVector (generatorI H) (seed hρ) t) ≤
    FactorTwoFinite.complexity (FactorTwoFinite.operatorSequence (generatorI H) (seed hρ))
      (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector (generatorI H) (seed hρ) t)
        (UnitaryEvolution.evolvedVector (generatorI H) (seed hρ) t))) ∧
    (2 * FactorTwoFinite.complexity (FactorTwoFinite.stateSequence (generatorU H) (seed hρ))
      (UnitaryEvolution.evolvedVector (generatorU H) (seed hρ) t) ≤
    FactorTwoFinite.complexity (FactorTwoFinite.operatorSequence (generatorU H) (seed hρ))
      (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector (generatorU H) (seed hρ) t)
        (UnitaryEvolution.evolvedVector (generatorU H) (seed hρ) t))) :=
  ⟨FactorTwoTheorem.finite_dimensional_factor_two _ (generatorI_hermitian hH) _
    (seed_unit hρ htrace) t,
   FactorTwoTheorem.finite_dimensional_factor_two _ (generatorU_hermitian hH) _
    (seed_unit hρ htrace) t⟩

def spread (G : Matrix (ι × ι) (ι × ι) ℂ) (s : ι × ι → ℂ) (t : ℝ) : ℝ :=
  FactorTwoFinite.complexity (FactorTwoFinite.stateSequence G s)
    (UnitaryEvolution.evolvedVector G s t)

def pureOperator (G : Matrix (ι × ι) (ι × ι) ℂ) (s : ι × ι → ℂ) (t : ℝ) : ℝ :=
  FactorTwoFinite.complexity (FactorTwoFinite.operatorSequence G s)
    (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector G s t)
      (UnitaryEvolution.evolvedVector G s t))

/-- Named I-branch corollary for its actual normalized initial purification. -/
theorem K_I_ge_two_S_I {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (s : ι × ι → ℂ) (hs : ‖UnitaryEvolution.hilbertVector s‖ = 1) (t : ℝ) :
    2 * spread (generatorI H) s t ≤ pureOperator (generatorI H) s t :=
  FactorTwoTheorem.finite_dimensional_factor_two _ (generatorI_hermitian hH) s hs t

/-- Named U*-branch corollary, with its different actual generator. -/
theorem K_U_ge_two_S_U {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (s : ι × ι → ℂ) (hs : ‖UnitaryEvolution.hilbertVector s‖ = 1) (t : ℝ) :
    2 * spread (generatorU H) s t ≤ pureOperator (generatorU H) s t :=
  FactorTwoTheorem.finite_dimensional_factor_two _ (generatorU_hermitian hH) s hs t

end
end Krylov.PurificationBranches
