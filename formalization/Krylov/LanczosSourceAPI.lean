import Krylov.WitnessProbabilityAPI

namespace Krylov.LanczosSourceAPI
open Matrix OperatorBridge ConcreteChains MatrixGSBridge WitnessSourceAPI
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000

abbrev actualVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (A : Operator ι) (n : ℕ) :=
  gramSchmidtNormed ℂ
    (PerturbedDynamics.powerSequence (PerturbedDynamics.liouvillian (hamiltonian E))
      (PhysicalCurvatureNecessary.normalizedSeed A)) n

lemma right_mixed_monic (i : Fin 3) : (RightMixed.polynomial i).Monic := by
  apply Polynomial.monic_of_degree_le i.val
    (by simpa [RightMixed.polynomial,ThreeAtomOperator.polynomial] using
      (CertifiedPolynomialDegrees.three (225/169) i).le)
  fin_cases i <;> norm_num [RightMixed.polynomial]

lemma right_purified_monic (i : Fin 5) : (PurifiedChain.polynomial i).Monic := by
  apply Polynomial.monic_of_degree_le i.val (right_purified_degree i).le
  fin_cases i <;> norm_num [PurifiedChain.polynomial,Polynomial.coeff_C_mul]

theorem right_mixed_vector (i : Fin 3) :
    actualVector States.energyR RightMixed.seed i.val =
      PhysicalCurvatureNecessary.normalizedSeed (RightMixed.chain i) := by
  apply CertifiedProbabilities.monic_normed_gram _ _
    (by simpa [RightMixed.chain_zero] using RightMixed.chain_nonzero 0)
    RightMixed.chain RightMixed.polynomial
  · intro i; rw [diagonal_commutator]; rfl
  · simpa [RightMixed.polynomial,ThreeAtomOperator.polynomial] using
      CertifiedPolynomialDegrees.three (225/169)
  · intro i j hij; simp [RightMixed.gram,hij]
  · exact right_mixed_monic

theorem right_purified_vector (i : Fin 5) :
    actualVector PurifiedChain.energies PurifiedChain.seed i.val =
      PhysicalCurvatureNecessary.normalizedSeed (PurifiedChain.chain i) := by
  apply CertifiedProbabilities.monic_normed_gram _ _
    (by intro hz; have h := PurifiedChain.seed_norm; simp [hz,hsInner] at h)
    PurifiedChain.chain PurifiedChain.polynomial
  · intro i; rw [diagonal_commutator]; rfl
  · exact right_purified_degree
  · intro i j hij; simp [PurifiedChain.gram,hij]
  · exact right_purified_monic

lemma hs_add {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C : Operator ι) :
    hsInner A (B+C)=hsInner A B+hsInner A C := by
  exact (hsInnerLinearRight A).map_add B C

lemma hs_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Operator ι) (c : ℂ) :
    hsInner A (c • B)=c*hsInner A B := by
  exact (hsInnerLinearRight A).map_smul c B

lemma hs_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Operator ι) :
    hsInner A 0 = 0 := (hsInnerLinearRight A).map_zero

theorem right_mixed_couplings (i j : Fin 3) :
    ‖⟪actualVector States.energyR RightMixed.seed i.val,
      PerturbedDynamics.liouvillian (hamiltonian States.energyR)
        (actualVector States.energyR RightMixed.seed j.val)⟫_ℂ‖^2 =
    if i.val=j.val+1 then Spectral.RightMixed.bSquared i else
      if j.val=i.val+1 then Spectral.RightMixed.bSquared j else 0 := by
  rw [right_mixed_vector,right_mixed_vector,CertifiedProbabilities.normalized_coupling,
    ← liouvillian_commutator,RightMixed.ordered_recurrence]
  fin_cases i <;> fin_cases j <;>
    norm_num [hs_add,hs_smul,hs_zero,RightMixed.gram,RightMixed.seed_norm,
      Spectral.RightMixed.norms,Spectral.RightMixed.bSquared,← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]

theorem right_purified_couplings (i j : Fin 5) :
    ‖⟪actualVector PurifiedChain.energies PurifiedChain.seed i.val,
      PerturbedDynamics.liouvillian (hamiltonian PurifiedChain.energies)
        (actualVector PurifiedChain.energies PurifiedChain.seed j.val)⟫_ℂ‖^2 =
    if i.val=j.val+1 then Spectral.RightPurified.bSquared i else
      if j.val=i.val+1 then Spectral.RightPurified.bSquared j else 0 := by
  rw [right_purified_vector,right_purified_vector,CertifiedProbabilities.normalized_coupling,
    ← liouvillian_commutator,PurifiedChain.ordered_recurrence]
  fin_cases i <;> fin_cases j <;>
    norm_num [hs_add,hs_smul,hs_zero,PurifiedChain.gram,PurifiedChain.seed_norm,
      Spectral.RightPurified.norms,Spectral.RightPurified.bSquared,← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]

end
end Krylov.LanczosSourceAPI
