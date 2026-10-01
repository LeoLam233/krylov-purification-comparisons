import Krylov.PerturbedDynamics

namespace Krylov.CubicRemainder
open PerturbedDynamics TaylorRemainder
open scoped InnerProductSpace
noncomputable section

/-- The manuscript's absolute-time cubic remainder, including negative times. -/
theorem quadratic_remainder_alltime {f : ℝ → ℝ} {k B : ℝ} (t : ℝ)
    (hf : ContDiff ℝ 3 f) (h0 : f 0=0) (h1 : deriv f 0=0)
    (h2 : iteratedDeriv 2 f 0=2*k) (hB : ∀ x,|iteratedDeriv 3 f x|≤B) :
    |f t-k*t^2| ≤ B*|t|^3/6 := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · let g : ℝ → ℝ := fun x => f (-x)
    have hg : ContDiff ℝ 3 g := hf.comp contDiff_id.neg
    have hg0 : g 0=0 := by simpa [g] using h0
    have hg1 : deriv g 0=0 := by simp [g,deriv_comp_neg,h1]
    have hg2 : iteratedDeriv 2 g 0=2*k := by
      simpa [g,iteratedDeriv_comp_neg] using h2
    have hgB : ∀ x,|iteratedDeriv 3 g x|≤B := by
      intro x
      simpa [g,iteratedDeriv_comp_neg,show (-1 : ℝ)^3 = -1 by norm_num] using hB (-x)
    have h := quadratic_remainder (t := -t) (by linarith) hg hg0 hg1 hg2
      (fun x _ => hgB x)
    simpa [g,abs_of_neg ht] using h
  · subst t
    simp [h0]
  · simpa [abs_of_pos ht] using quadratic_remainder ht hf h0 h1 h2 (fun x _ => hB x)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]


/-- The generic source expectation bound does not assume a centered seed.
Its quadratic coefficient is defined by the actual second derivative. -/
theorem expectation_cubic_remainder (L N : E →L[ℂ] E)
    (hL : IsSelfAdjoint L) (hN : IsSelfAdjoint N) (v : E)
    (hv : ‖v‖=1) (hNv : N v=0) (t : ℝ) :
    |expectation (skewGenerator L) N v t -
      (iteratedDeriv 2 (expectation (skewGenerator L) N v) 0/2)*t^2| ≤
      ((2*‖L‖)^3*‖N‖)*|t|^3/6 := by
  have hleft (x : E) : ⟪v,N x⟫_ℂ=0 := by
    have he : ⟪N v,x⟫_ℂ = ⟪v,N x⟫_ℂ :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hN) v x
    rw [hNv,inner_zero_left] at he
    exact he.symm
  have h0 : expectation (skewGenerator L) N v 0=0 := by simp [expectation,hNv]
  have h1 : deriv (expectation (skewGenerator L) N v) 0=0 := by
    rw [(expectation_hasDerivAt (skewGenerator L) N v 0).deriv]
    simp [expectation,derivativeOperator,ContinuousLinearMap.mul_apply,
      inner_add_right,ContinuousLinearMap.adjoint_inner_right,hNv,hleft]
  apply quadratic_remainder_alltime t (expectation_contDiff _ _ _ 3) h0 h1 (by ring)
  intro x
  have hb := abs_iteratedDeriv_le (skewGenerator L) N v 3 x
    (by rw [evolution_norm L hL,hv])
  simpa [skewGenerator,norm_smul] using hb

/-- Generic actual finite Krylov complexity, with no zero-mean restriction. -/
theorem actual_cubic_remainder_general (L : E →L[ℂ] E) (hL : IsSelfAdjoint L)
    (v : E) (hv : ‖v‖=1) (t : ℝ) :
    |actualComplexity L v t - (iteratedDeriv 2 (actualComplexity L v) 0/2)*t^2| ≤
      ((2*‖L‖)^3*‖numberOperator (powerSequence L v)‖)*|t|^3/6 := by
  rw [actualComplexity_eq_expectation]
  apply expectation_cubic_remainder L _ hL (numberOperator_selfAdjoint _) v hv _ t
  simpa [powerSequence] using numberOperator_seed (powerSequence L v)

theorem actual_cubic_remainder (L : E →L[ℂ] E) (hL : IsSelfAdjoint L)
    (v : E) (hv : ‖v‖=1) (hov : ⟪v,L v⟫_ℂ=0) (t : ℝ) :
    |actualComplexity L v t-‖L v‖^2*t^2| ≤
      ((2*‖L‖)^3*‖numberOperator (powerSequence L v)‖)*|t|^3/6 := by
  obtain ⟨h0,h1,h2⟩ := actual_initial_data L v hov
  apply quadratic_remainder_alltime t (actualComplexity_contDiff L v 3) h0 h1 h2
  intro x
  rw [actualComplexity_eq_expectation]
  have h := abs_iteratedDeriv_le (skewGenerator L) (numberOperator (powerSequence L v)) v 3 x
    (by rw [evolution_norm L hL,hv])
  simpa [skewGenerator,norm_smul] using h

theorem actual_cubic_remainder_11_5_six (L : E →L[ℂ] E) (hL : IsSelfAdjoint L)
    (v : E) (hv : ‖v‖=1) (hov : ⟪v,L v⟫_ℂ=0)
    (hLn : ‖L‖≤11/5) (hN : ‖numberOperator (powerSequence L v)‖≤6) (t : ℝ) :
    |actualComplexity L v t-‖L v‖^2*t^2| ≤ (10648/125)*|t|^3 := by
  have h := actual_cubic_remainder L hL v hv hov t
  have hc : (2*‖L‖)^3*‖numberOperator (powerSequence L v)‖ ≤ (2*(11/5 : ℝ))^3*6 := by
    gcongr
  calc
    _ ≤ ((2*‖L‖)^3*‖numberOperator (powerSequence L v)‖)*|t|^3/6 := h
    _ ≤ ((2*(11/5 : ℝ))^3*6)*|t|^3/6 := by gcongr
    _ = _ := by ring
end
end Krylov.CubicRemainder
