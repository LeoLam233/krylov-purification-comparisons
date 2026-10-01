import Mathlib

/-! Taylor bounds for genuine bounded-operator exponential expectation curves.
The derivatives are calculated from the exponential and adjoint, rather than
postulated as an approximation hypothesis. -/
namespace Krylov.TaylorRemainder
open scoped InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 2000000

section Expectation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def evolution (A : E →L[ℂ] E) (v : E) (t : ℝ) : E :=
  NormedSpace.exp ℝ (t • A) v

def expectation (A N : E →L[ℂ] E) (v : E) (t : ℝ) : ℝ :=
  (⟪evolution A v t, N (evolution A v t)⟫_ℂ).re

def derivativeOperator (A N : E →L[ℂ] E) : E →L[ℂ] E :=
  N * A + ContinuousLinearMap.adjoint A * N

def derivativeIterate (A N : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E :=
  (derivativeOperator A)^[n] N

@[simp] theorem evolution_zero (A : E →L[ℂ] E) (v : E) : evolution A v 0 = v := by
  simp [evolution]

theorem evolution_hasDerivAt (A : E →L[ℂ] E) (v : E) (t : ℝ) :
    HasDerivAt (evolution A v) (A (evolution A v t)) t := by
  have h := (((ContinuousLinearMap.apply ℂ E) v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' A t)
  simpa [evolution, Function.comp_def, ContinuousLinearMap.mul_apply] using h

theorem expectation_hasDerivAt (A N : E →L[ℂ] E) (v : E) (t : ℝ) :
    HasDerivAt (expectation A N v) (expectation A (derivativeOperator A N) v t) t := by
  have h := evolution_hasDerivAt A v t
  have hN := (N.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h
  have hi := h.inner ℂ hN
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hi
  convert hr using 1
  simp only [expectation, derivativeOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.mul_apply, inner_add_right,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

@[simp] theorem derivativeIterate_zero (A N : E →L[ℂ] E) : derivativeIterate A N 0 = N := rfl

@[simp] theorem derivativeIterate_succ (A N : E →L[ℂ] E) (n : ℕ) :
    derivativeIterate A N (n+1) = derivativeOperator A (derivativeIterate A N n) := by
  simp [derivativeIterate, Function.iterate_succ_apply']

theorem iteratedDeriv_expectation (A N : E →L[ℂ] E) (v : E) (n : ℕ) :
    iteratedDeriv n (expectation A N v) = expectation A (derivativeIterate A N n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, derivativeIterate_succ]
    funext t
    exact (expectation_hasDerivAt A _ v t).deriv

/-- The actual expectation of a bounded-operator exponential is smooth to
every finite order, with no supplied regularity hypothesis. -/
theorem expectation_contDiff (A N : E →L[ℂ] E) (v : E) (n : ℕ) :
    ContDiff ℝ n (expectation A N v) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro m _
    rw [iteratedDeriv_expectation]
    exact continuous_iff_continuousAt.mpr (fun t => (expectation_hasDerivAt A _ v t).continuousAt)
  · intro m _
    rw [iteratedDeriv_expectation]
    exact fun t => (expectation_hasDerivAt A _ v t).differentiableAt

theorem norm_derivativeOperator_le (A N : E →L[ℂ] E) :
    ‖derivativeOperator A N‖ ≤ (2*‖A‖)*‖N‖ := by
  calc
    ‖derivativeOperator A N‖ ≤ ‖N*A‖ + ‖ContinuousLinearMap.adjoint A*N‖ := norm_add_le _ _
    _ ≤ ‖N‖*‖A‖ + ‖ContinuousLinearMap.adjoint A‖*‖N‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = (2*‖A‖)*‖N‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

theorem norm_derivativeIterate_le (A N : E →L[ℂ] E) (n : ℕ) :
    ‖derivativeIterate A N n‖ ≤ (2*‖A‖)^n*‖N‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [derivativeIterate_succ]
    calc
      _ ≤ (2*‖A‖)*‖derivativeIterate A N n‖ := norm_derivativeOperator_le _ _
      _ ≤ (2*‖A‖)*((2*‖A‖)^n*‖N‖) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (2*‖A‖)^(n+1)*‖N‖ := by ring

theorem abs_expectation_le (A N : E →L[ℂ] E) (v : E) (t : ℝ) :
    |expectation A N v t| ≤ ‖N‖*‖evolution A v t‖^2 := by
  calc
    _ ≤ ‖⟪evolution A v t, N (evolution A v t)⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖evolution A v t‖ * ‖N (evolution A v t)‖ := norm_inner_le_norm _ _
    _ ≤ ‖evolution A v t‖ * (‖N‖*‖evolution A v t‖) :=
      mul_le_mul_of_nonneg_left (N.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

/-- The source derivative estimate follows for the actual expectation curve
whenever its evolved seed has unit norm. -/
theorem abs_iteratedDeriv_le (A N : E →L[ℂ] E) (v : E) (n : ℕ) (t : ℝ)
    (hu : ‖evolution A v t‖ = 1) :
    |iteratedDeriv n (expectation A N v) t| ≤ (2*‖A‖)^n*‖N‖ := by
  rw [iteratedDeriv_expectation]
  exact (abs_expectation_le A _ v t).trans (by simpa [hu] using norm_derivativeIterate_le A N n)

/-- The first three Taylor data are derived from the number operator killing
its seed and acting as degree one on the initial velocity. -/
theorem expectation_initial_data (A N : E →L[ℂ] E) (v : E)
    (hN : N v = 0) (hleft : ∀ x, ⟪v, N x⟫_ℂ = 0) (hvel : N (A v) = A v) :
    expectation A N v 0 = 0 ∧ deriv (expectation A N v) 0 = 0 ∧
      iteratedDeriv 2 (expectation A N v) 0 = 2*‖A v‖^2 := by
  constructor
  · simp [expectation,hN]
  constructor
  · rw [(expectation_hasDerivAt A N v 0).deriv]
    simp [expectation,derivativeOperator,ContinuousLinearMap.mul_apply,
      inner_add_right,ContinuousLinearMap.adjoint_inner_right,hN,hleft]
  · rw [iteratedDeriv_expectation]
    simp [expectation,derivativeIterate_succ,derivativeOperator,
      ContinuousLinearMap.mul_apply,inner_add_right,
      ContinuousLinearMap.adjoint_inner_right,hN,hleft,hvel,
      inner_self_eq_norm_sq_to_K,←Complex.ofReal_pow]
    ring_nf

/-- The cubic coefficient vanishes for a skew-adjoint generator and a
selfadjoint number operator assigning degree one to the initial velocity. -/
theorem expectation_third_zero (A N : E →L[ℂ] E) (v : E)
    (hA : ContinuousLinearMap.adjoint A = -A)
    (hN : N v = 0) (hleft : ∀ x, ⟪v,N x⟫_ℂ=0)
    (hsym : ∀ x y, ⟪x,N y⟫_ℂ=⟪N x,y⟫_ℂ)
    (hvel : N (A v)=A v) : iteratedDeriv 3 (expectation A N v) 0=0 := by
  have hskew (x y : E) : ⟪A x,y⟫_ℂ = -⟪x,A y⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right,hA]
    simp
  have hvleft (x : E) : ⟪A v,N x⟫_ℂ = ⟪A v,x⟫_ℂ := by rw [hsym,hvel]
  rw [iteratedDeriv_expectation]
  simp only [expectation,evolution_zero,derivativeIterate_succ,derivativeIterate_zero,
    derivativeOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.mul_apply,
    map_add,inner_add_right,ContinuousLinearMap.adjoint_inner_right,hN,map_zero,
    inner_zero_right,hleft,zero_add,add_zero,hvleft,hvel]
  rw [hskew (A v) (A v)]
  simp

end Expectation

section Intertwining
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Exponentials respect an actual continuous linear intertwiner; proved
from the convergent series, so it also applies across different matrix norms. -/
theorem exponential_intertwining (T : E →L[ℂ] F) (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (h : ∀ x,T (A x)=B (T x)) (v : E) (c : ℂ) :
    T (NormedSpace.exp ℂ (c • A) v) = NormedSpace.exp ℂ (c • B) (T v) := by
  have hp (n : ℕ) : T ((A^n) v)=(B^n) (T v) := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',pow_succ',ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.mul_apply,h,ih]
  have hs1 := ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • A)).map
    ((ContinuousLinearMap.apply ℂ E) v) ((ContinuousLinearMap.apply ℂ E) v).continuous).map T T.continuous
  have hs2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • B)).map
    ((ContinuousLinearMap.apply ℂ F) (T v)) ((ContinuousLinearMap.apply ℂ F) (T v)).continuous
  have h1 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (c^n • ((B^n) (T v))))
      (T (NormedSpace.exp ℂ (c • A) v)) := by
    simpa [Function.comp_def,smul_pow,ContinuousLinearMap.smul_apply,map_smul,hp] using hs1
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (c^n • ((B^n) (T v))))
      (NormedSpace.exp ℂ (c • B) (T v)) := by
    simpa [Function.comp_def,smul_pow,ContinuousLinearMap.smul_apply] using hs2
  exact h1.unique h2
end Intertwining

section Scalar

/-- Within-interval derivatives agree with the global derivative tower. -/
theorem iteratedDerivWithin_eq_of_tower {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℕ → ℝ → F) (hd : ∀ n t, HasDerivAt (d n) (d (n+1) t) t)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (n : ℕ) {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin n (d 0) s x = d n x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDerivWithin_succ]
    rw [derivWithin_congr (fun y hy => ih hy) (ih hx)]
    exact (hd n x).hasDerivWithinAt.derivWithin (hs x hx)

theorem quadratic_remainder {f : ℝ → ℝ} {k B t : ℝ}
    (ht : 0 < t) (hf : ContDiff ℝ 3 f)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 0) (h2 : iteratedDeriv 2 f 0 = 2*k)
    (hB : ∀ x ∈ Set.Icc 0 t, |iteratedDeriv 3 f x| ≤ B) :
    |f t-k*t^2| ≤ B*t^3/6 := by
  have hd : ∀ n x, n < 3 → HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f x) x := by
    intro n x hn
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv n (by exact_mod_cast hn) x).hasDerivAt
  have he : ∀ n ≤ 3, ∀ x ∈ Set.Icc 0 t,
      iteratedDerivWithin n f (Set.Icc 0 t) x = iteratedDeriv n f x := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      rw [iteratedDerivWithin_succ]
      rw [derivWithin_congr (fun y hy => ih (by omega) y hy) (ih (by omega) x hx)]
      exact (hd n x (by omega)).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc ht x hx)
  have hc : ContDiffOn ℝ (2 : ℕ) f (Set.Icc 0 t) := (hf.of_le (by exact_mod_cast (by norm_num : (2:ℕ) ≤ 3))).contDiffOn
  have hd2 : DifferentiableOn ℝ (iteratedDerivWithin 2 f (Set.Icc 0 t)) (Set.Ioo 0 t) := by
    intro x hx
    apply DifferentiableWithinAt.congr (s := Set.Ioo 0 t)
      ((hf.differentiable_iteratedDeriv 2 (by exact_mod_cast (by norm_num : (2:ℕ) < 3)) x).differentiableWithinAt)
    · intro y hy
      exact he 2 (by omega) y (Set.Ioo_subset_Icc_self hy)
    · exact he 2 (by omega) x (Set.Ioo_subset_Icc_self hx)
  obtain ⟨x,hx,hr⟩ := taylor_mean_remainder_lagrange (n := 2) ht hc hd2
  have hp : taylorWithinEval f 2 (Set.Icc 0 t) 0 t = k*t^2 := by
    rw [show 2=1+1 from rfl,taylorWithinEval_succ,taylorWithinEval_succ,taylor_within_zero_eval]
    rw [he 2 (by omega) 0 (by constructor <;> linarith),
      he 1 (by omega) 0 (by constructor <;> linarith)]
    simp [h0,h1,h2]
    ring_nf
  rw [hp, he 3 (by omega) x (Set.Ioo_subset_Icc_self hx)] at hr
  rw [hr]
  norm_num [abs_div,abs_mul,abs_of_nonneg (by positivity : 0 ≤ t^3)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hB x (Set.Ioo_subset_Icc_self hx))
    (by positivity)) (by norm_num)
theorem quartic_remainder {f : ℝ → ℝ} {k B t : ℝ}
    (ht : 0 < t) (hf : ContDiff ℝ 4 f)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 0) (h2 : iteratedDeriv 2 f 0 = 2*k)
    (h3 : iteratedDeriv 3 f 0 = 0)
    (hB : ∀ x ∈ Set.Icc 0 t, |iteratedDeriv 4 f x| ≤ B) :
    |f t-k*t^2| ≤ B*t^4/24 := by
  have hd : ∀ n x, n < 4 → HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f x) x := by
    intro n x hn
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv n (by exact_mod_cast hn) x).hasDerivAt
  have he : ∀ n ≤ 4, ∀ x ∈ Set.Icc 0 t,
      iteratedDerivWithin n f (Set.Icc 0 t) x = iteratedDeriv n f x := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      rw [iteratedDerivWithin_succ]
      rw [derivWithin_congr (fun y hy => ih (by omega) y hy) (ih (by omega) x hx)]
      exact (hd n x (by omega)).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc ht x hx)
  have hc : ContDiffOn ℝ (3 : ℕ) f (Set.Icc 0 t) := (hf.of_le (by exact_mod_cast (by norm_num : (3:ℕ) ≤ 4))).contDiffOn
  have hd3 : DifferentiableOn ℝ (iteratedDerivWithin 3 f (Set.Icc 0 t)) (Set.Ioo 0 t) := by
    intro x hx
    apply DifferentiableWithinAt.congr (s := Set.Ioo 0 t)
      ((hf.differentiable_iteratedDeriv 3 (by exact_mod_cast (by norm_num : (3:ℕ) < 4)) x).differentiableWithinAt)
    · intro y hy
      exact he 3 (by omega) y (Set.Ioo_subset_Icc_self hy)
    · exact he 3 (by omega) x (Set.Ioo_subset_Icc_self hx)
  obtain ⟨x,hx,hr⟩ := taylor_mean_remainder_lagrange (n := 3) ht hc hd3
  have hp : taylorWithinEval f 3 (Set.Icc 0 t) 0 t = k*t^2 := by
    rw [show 3=2+1 from rfl,taylorWithinEval_succ,taylorWithinEval_succ,taylorWithinEval_succ,taylor_within_zero_eval]
    rw [he 3 (by omega) 0 (by constructor <;> linarith),
      he 2 (by omega) 0 (by constructor <;> linarith),
      he 1 (by omega) 0 (by constructor <;> linarith)]
    simp [h0,h1,h2,h3]
    ring_nf
  rw [hp, he 4 (by omega) x (Set.Ioo_subset_Icc_self hx)] at hr
  rw [hr]
  norm_num [abs_div,abs_mul,abs_of_nonneg (by positivity : 0 ≤ t^4)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hB x (Set.Ioo_subset_Icc_self hx))
    (by positivity)) (by norm_num)
theorem positive_quadratic_minus_quartic {k B : ℝ} (hk : 0<k) (hB : 0≤B) :
    ∃ ε>0, ∀ t : ℝ, 0<t → t<ε → 0<k*t^2-B*t^4 := by
  refine ⟨min 1 (k/(B+1)),lt_min (by norm_num) (div_pos hk (by linarith)),?_⟩
  intro t ht he
  have ht1 : t<1 := lt_of_lt_of_le he (min_le_left _ _)
  have htk : t<k/(B+1) := lt_of_lt_of_le he (min_le_right _ _)
  have hm : t*(B+1)<k := (lt_div_iff₀ (by linarith : 0<B+1)).mp htk
  have hbt : B*t^2<k := by
    have hmul := mul_nonneg hB (show 0≤t-t^2 by nlinarith)
    nlinarith
  have hp := mul_pos (sub_pos.mpr hbt) (sq_pos_of_pos ht)
  nlinarith

end Scalar
end
end Krylov.TaylorRemainder
