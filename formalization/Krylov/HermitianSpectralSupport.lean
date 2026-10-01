import Krylov.FiniteSpectralSupport
import Krylov.UniversalQubit

namespace Krylov.HermitianSpectralSupport
open Matrix ConcreteChains FiniteSpectralSupport UniversalQubit UnitaryCovariance
noncomputable section
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateEquiv {H : Matrix ι ι ℂ} (hH : H.IsHermitian) : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
  { (energyBasis hH)ᴴ.mulVecLin with
    invFun := fun x => energyBasis hH *ᵥ x
    left_inv := by intro x; simp [mulVec_mulVec,energyBasis_unitary_reverse hH]
    right_inv := by intro x; simp [mulVec_mulVec,energyBasis_unitary hH] }

@[simp] lemma coordinateEquiv_apply {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (v : ι → ℂ) :
    coordinateEquiv hH v = (energyBasis hH)ᴴ *ᵥ v := rfl

lemma intertwines {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (v : ι → ℂ) :
    coordinateEquiv hH (H.mulVecLin v) =
      diagonalEnd (fun i => (hH.eigenvalues i : ℂ)) (coordinateEquiv hH v) := by
  have he : (energyBasis hH)ᴴ*H = OperatorBridge.hamiltonian hH.eigenvalues*(energyBasis hH)ᴴ := by
    rw [← hamiltonian_coordinates hH]
    simp [changeBasis,mul_assoc,energyBasis_unitary_reverse hH]
  change (energyBasis hH)ᴴ *ᵥ (H *ᵥ v) = _
  rw [mulVec_mulVec,he,← mulVec_mulVec]
  ext i
  simp [diagonalEnd,OperatorBridge.hamiltonian,Matrix.mulVec_diagonal]

lemma power_coordinates {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (v : ι → ℂ) (k : ℕ) :
    coordinateEquiv hH ((H.mulVecLin^k) v) =
      ((diagonalEnd (fun i => (hH.eigenvalues i : ℂ)))^k) (coordinateEquiv hH v) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ',Module.End.mul_apply,intertwines,ih,pow_succ',Module.End.mul_apply]

lemma cyclic_coordinates {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (v : ι → ℂ) :
    (cyclicSpan H.mulVecLin v).map (coordinateEquiv hH).toLinearMap =
      cyclicSpan (diagonalEnd (fun i => (hH.eigenvalues i : ℂ))) (coordinateEquiv hH v) := by
  unfold cyclicSpan
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y,⟨k,rfl⟩,rfl⟩
    exact ⟨k,(power_coordinates hH v k).symm⟩
  · rintro ⟨k,rfl⟩
    exact ⟨(H.mulVecLin^k) v,⟨k,rfl⟩,power_coordinates hH v k⟩

/-- Full arbitrary-Hermitian version of the source's exact positive spectral
support/chain-length assertion, with the actual eigenbasis supplied internally. -/
theorem cyclic_dimension {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (v : ι → ℂ) :
    Module.finrank ℂ (cyclicSpan H.mulVecLin v) =
      (atoms (fun i => (hH.eigenvalues i : ℂ)) ((energyBasis hH)ᴴ *ᵥ v)).card := by
  rw [← (coordinateEquiv hH).finrank_map_eq,cyclic_coordinates]
  exact FiniteSpectralSupport.cyclic_dimension _ _
end
end Krylov.HermitianSpectralSupport
