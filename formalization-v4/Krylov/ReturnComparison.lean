import Krylov.Bounds

/-! The manuscript's return-loss ratio corollary for arbitrary normalized
finite chains. The statement directly uses their actual index-weighted sums. -/
namespace Krylov.ReturnComparison
open scoped BigOperators
noncomputable section

theorem finite_chain_ratio_bounds (NS NK : ℕ)
    (pS : Fin (NS+1) → ℝ) (pK : Fin (NK+1) → ℝ)
    (hpS : ∀ i,0 ≤ pS i) (hpK : ∀ i,0 ≤ pK i)
    (hsS : ∑ i,pS i=1) (hsK : ∑ i,pK i=1)
    (AS AK : ℂ) (haS : pS 0=‖AS‖^2) (haK : pK 0=‖AK‖^2)
    (hlS : 0 < 1-‖AS‖^2) (hlK : 0 < 1-‖AK‖^2) :
    (1-‖AS‖^2)/((NK:ℝ)*(1-‖AK‖^2)) ≤
      finiteComplexity NS pS / finiteComplexity NK pK ∧
    finiteComplexity NS pS / finiteComplexity NK pK ≤
      ((NS:ℝ)*(1-‖AS‖^2))/(1-‖AK‖^2) := by
  obtain ⟨hSlo,hShi⟩ := finite_return_amplitude_bounds NS pS hpS hsS AS haS
  obtain ⟨hKlo,hKhi⟩ := finite_return_amplitude_bounds NK pK hpK hsK AK haK
  have hKpos : 0 < finiteComplexity NK pK := hlK.trans_le hKlo
  constructor
  · exact (div_le_div_of_nonneg_left hlS.le hKpos hKhi).trans
      (div_le_div_of_nonneg_right hSlo hKpos.le)
  · exact (div_le_div_of_nonneg_right hShi hKpos.le).trans
      (div_le_div_of_nonneg_left (by positivity) hlK hKlo)
end
end Krylov.ReturnComparison
