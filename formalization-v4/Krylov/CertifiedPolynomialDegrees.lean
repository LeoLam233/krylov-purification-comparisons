import Krylov.FiveAtom

/-! Degree certificates for the small reusable three- and five-atom families. -/
namespace Krylov.CertifiedPolynomialDegrees
open Polynomial
noncomputable section

lemma three (μ : ℝ) (k : Fin 3) :
    (ThreeAtomOperator.polynomial μ k).degree=(k.val : WithBot ℕ) := by
  fin_cases k
  · simp [ThreeAtomOperator.polynomial]
  · simp [ThreeAtomOperator.polynomial]
  · exact degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ)) (μ : ℂ)

lemma leading_cubic (a b : ℂ) (ha : a ≠ 0) :
    (C a * X^3-C b * X).degree=(3 : WithBot ℕ) := by
  rw [degree_sub_eq_left_of_degree_lt]
  · simpa using degree_C_mul_X_pow 3 ha
  · rw [degree_C_mul_X_pow 3 ha]
    exact (degree_C_mul_X_le b).trans_lt (by norm_num)

lemma leading_quartic (a b c : ℂ) (ha : a ≠ 0) :
    (C a * X^4-C b * X^2+C c).degree=(4 : WithBot ℕ) := by
  have hh : (C a * X^4-C b * X^2).degree=(4 : WithBot ℕ) := by
    rw [degree_sub_eq_left_of_degree_lt]
    · simpa using degree_C_mul_X_pow 4 ha
    · rw [degree_C_mul_X_pow 4 ha]
      exact (degree_C_mul_X_pow_le 2 b).trans_lt (by norm_num)
  rw [degree_add_eq_left_of_degree_lt,hh]
  rw [hh]
  exact degree_C_le.trans_lt (by norm_num)

lemma five (u v : ℝ) (hm : FiveAtom.m2 u v ≠ 0) (hn : FiveAtom.n2 u v ≠ 0)
    (k : Fin 5) : (FiveAtom.polynomial u v k).degree=(k.val : WithBot ℕ) := by
  have hmc : (FiveAtom.m2 u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
  have hnc : (FiveAtom.n2 u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  fin_cases k
  · simp [FiveAtom.polynomial]
  · simp [FiveAtom.polynomial]
  · exact degree_X_pow_sub_C (by norm_num : 0 < (2 : ℕ)) (FiveAtom.m2 u v : ℂ)
  · exact leading_cubic _ _ hmc
  · exact leading_quartic _ _ _ hnc

end
end Krylov.CertifiedPolynomialDegrees
