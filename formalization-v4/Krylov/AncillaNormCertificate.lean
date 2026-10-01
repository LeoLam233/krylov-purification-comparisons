import Krylov.RationalPowerCertificates
import Krylov.PurifiedCovariance

namespace Krylov.AncillaNormCertificate
open Matrix PerturbedDynamics
open scoped BigOperators Kronecker
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem frobenius_reindex (e : ι ≃ κ) (B : Matrix ι ι ℂ) :
    (∑ i,∑ j,‖(Matrix.reindex e e B) i j‖^2) = ∑ i,∑ j,‖B i j‖^2 := by
  change (∑ i,∑ j,‖B (e.symm i) (e.symm j)‖^2) = _
  calc
    _ = ∑ i,∑ j : ι,‖B (e.symm i) j‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.symm.sum_comp (fun j => ‖B (e.symm i) j‖^2)
    _ = _ := e.symm.sum_comp (fun i => ∑ j,‖B i j‖^2)

theorem frobenius_kronecker_one (B : Matrix ι ι ℂ) :
    (∑ a : ι×κ,∑ b : ι×κ,‖(B ⊗ₖ (1 : Matrix κ κ ℂ)) a b‖^2) =
      (Fintype.card κ : ℝ)*(∑ i,∑ j,‖B i j‖^2) := by
  simp [Fintype.sum_prod_type,kronecker_apply,Matrix.one_apply,mul_ite,
    Finset.mul_sum,Finset.sum_mul,apply_ite,ite_pow]

theorem kronecker_one_pow (B : Matrix ι ι ℂ) (n : ℕ) :
    (B ⊗ₖ (1 : Matrix κ κ ℂ))^n = (B^n) ⊗ₖ (1 : Matrix κ κ ℂ) := by
  induction n with
  | zero => simp [Matrix.one_kronecker_one]
  | succ n ih =>
    rw [pow_succ,ih,← Matrix.mul_kronecker_mul,one_mul,pow_succ]

def shuffle : ((ι×κ)×(ι×κ)) ≃ ((ι×ι)×(κ×κ)) := Equiv.prodProdProdComm ι κ ι κ

theorem lifted_commutator (G : Matrix ι ι ℂ) :
    commutatorMatrix (G ⊗ₖ (1 : Matrix κ κ ℂ)) =
      Matrix.reindexAlgEquiv ℂ ℂ (shuffle (ι := ι) (κ := κ)).symm
        (commutatorMatrix G ⊗ₖ (1 : Matrix (κ×κ) (κ×κ) ℂ)) := by
  ext ⟨⟨i,j⟩,⟨k,l⟩⟩ ⟨⟨m,n⟩,⟨p,q⟩⟩
  by_cases h1 : i=m <;> by_cases h2 : k=p <;>
    by_cases h3 : j=n <;> by_cases h4 : l=q <;>
    simp [commutatorMatrix,Matrix.reindexAlgEquiv_apply,Matrix.reindex_apply,
      shuffle,Equiv.prodProdProdComm,kronecker_apply,Matrix.one_apply,
      h1,h2,h3,h4,eq_comm]

theorem lifted_power_frobenius (G : Matrix ι ι ℂ) (n : ℕ) :
    (∑ a,∑ b,‖((commutatorMatrix (G ⊗ₖ (1 : Matrix κ κ ℂ)))^n) a b‖^2) =
      (Fintype.card (κ×κ) : ℝ)*(∑ a,∑ b,‖((commutatorMatrix G)^n) a b‖^2) := by
  rw [lifted_commutator,← map_pow,kronecker_one_pow]
  change (∑ a,∑ b,‖(Matrix.reindex _ _ _) a b‖^2) = _
  rw [frobenius_reindex,frobenius_kronecker_one]

/-- Exact ancillary-block certificate bounds the original purified Liouvillian,
not the easier unpurified generator. -/
theorem purified_liouvillian_sharp_bound : ‖liouvillian (purifiedGenerator (1/20))‖ ≤ 11/5 := by
  apply PowerNormCertificate.norm_le_of_power_frobenius
    (commutatorMatrix (purifiedGenerator (1/20)))
    (commutatorMatrix_hermitian _ (purifiedGenerator_hermitian _)) 5 (11/5) (by norm_num)
  rw [show (2:ℕ)^5 = 32 from rfl]
  rw [show purifiedGenerator (1/20) = RationalPowerCertificates.H ⊗ₖ
    (1 : Matrix (Fin 3) (Fin 3) ℂ) from rfl]
  rw [lifted_power_frobenius]
  rw [show commutatorMatrix RationalPowerCertificates.H = RationalPowerCertificates.L from rfl,
    RationalPowerCertificates.l32_frobenius]
  norm_num
end
end Krylov.AncillaNormCertificate
