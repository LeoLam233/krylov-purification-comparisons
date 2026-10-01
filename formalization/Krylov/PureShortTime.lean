import Krylov.PerturbedDynamics
import Krylov.FactorTwoTheorem

namespace Krylov.PureShortTime
open Matrix FactorTwoFinite PerturbedDynamics TaylorRemainder
open scoped InnerProductSpace BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The degree operator removes precisely the seed component from the first
power. The first moment need not vanish. -/
theorem numberOperator_first_general (f : ℕ → E) (hu : ‖f 0‖ = 1) :
    numberOperator f (f 1) = f 1 - ⟪f 0,f 1⟫_ℂ • f 0 := by
  let w := f 1 - ⟪f 0,f 1⟫_ℂ • f 0
  have horth : ⟪f 0,w⟫_ℂ = 0 := by
    simp [w, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
  have hzero (k : GSIndex f) (hk : k.val ≠ 1) : ⟪gsFamily f k,w⟫_ℂ = 0 := by
    by_cases hk0 : k.val = 0
    · have hz : gramSchmidt ℂ f 0 = f 0 := gramSchmidt_zero ℂ f
      simp only [gsFamily,gramSchmidtNormed,hk0,hz,inner_smul_left,horth,mul_zero]
    · have h1 : ⟪gsFamily f k,f 1⟫_ℂ = 0 := by
        simp only [gsFamily,gramSchmidtNormed,inner_smul_left,
          gramSchmidt_inv_triangular ℂ f (show 1 < k.val by omega),mul_zero]
      simp only [w,inner_sub_right,inner_smul_right,h1,gs_inner_seed f hk0,
        mul_zero,sub_zero]
  have hcyclic : w ∈ cyclicSpan f := by
    apply Submodule.sub_mem
    · exact Submodule.subset_span ⟨1,rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩)
  have hw : numberOperator f w = w := by
    rw [numberOperator_apply]
    calc
      _ = ∑ k : GSIndex f, ⟪gsFamily f k,w⟫_ℂ • gsFamily f k := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k.val=1
        · simp [hk]
        · simp [hzero k hk]
      _ = w := cyclic_reconstruction f w hcyclic
  simpa only [w,map_sub,map_smul,numberOperator_seed,smul_zero,sub_zero] using hw

/-- Variance expressed without assuming the first moment is zero. For a
selfadjoint generator the squared modulus here is the squared real mean. -/
def variance (L : E →L[ℂ] E) (v : E) : ℝ := ‖L v‖^2 - ‖⟪v,L v⟫_ℂ‖^2

lemma initial_velocity_expectation (L : E →L[ℂ] E) (v : E) (hu : ‖v‖=1) :
    (⟪skewGenerator L v,
      numberOperator (powerSequence L v) (skewGenerator L v)⟫_ℂ).re = variance L v := by
  have hfirst := numberOperator_first_general (powerSequence L v) (by simpa [powerSequence] using hu)
  have hN : numberOperator (powerSequence L v) (L v) = L v - ⟪v,L v⟫_ℂ • v := by
    simpa [powerSequence] using hfirst
  have hi : ⟪skewGenerator L v,
      numberOperator (powerSequence L v) (skewGenerator L v)⟫_ℂ =
      ⟪L v,L v - ⟪v,L v⟫_ℂ • v⟫_ℂ := by
    simp only [skewGenerator,ContinuousLinearMap.smul_apply,map_smul,
      inner_smul_left,inner_smul_right,hN]
    rw [← mul_assoc]
    norm_num [Complex.star_def,Complex.I_sq]
    simp only [inner_sub_right,inner_smul_right]
  rw [hi,inner_sub_right,inner_smul_right,← inner_conj_symm (L v) v,
    Complex.mul_conj']
  simp [variance,inner_self_eq_norm_sq_to_K,Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_pow]

/-- All three leading Taylor data for the actual normalized Gram–Schmidt
complexity, with no centered-seed hypothesis. -/
theorem actual_initial_data_general (L : E →L[ℂ] E) (v : E) (hu : ‖v‖=1) :
    actualComplexity L v 0 = 0 ∧ deriv (actualComplexity L v) 0 = 0 ∧
      iteratedDeriv 2 (actualComplexity L v) 0 = 2*variance L v := by
  rw [actualComplexity_eq_expectation]
  have hN : numberOperator (powerSequence L v) v=0 := by
    simpa [powerSequence] using numberOperator_seed (powerSequence L v)
  have hleft : ∀ x, ⟪v,numberOperator (powerSequence L v) x⟫_ℂ=0 := by
    intro x
    simpa [powerSequence] using seed_inner_numberOperator (powerSequence L v) x
  constructor
  · simp [expectation,hN]
  constructor
  · rw [(expectation_hasDerivAt _ _ v 0).deriv]
    simp [expectation,derivativeOperator,ContinuousLinearMap.mul_apply,
      inner_add_right,ContinuousLinearMap.adjoint_inner_right,hN,hleft]
  · rw [iteratedDeriv_expectation]
    simp only [expectation,evolution_zero,derivativeIterate_succ,
      derivativeIterate_zero,derivativeOperator,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply,map_add,inner_add_right,
      ContinuousLinearMap.adjoint_inner_right,hN,map_zero,
      inner_zero_right,hleft,zero_add,add_zero,Complex.add_re,
      initial_velocity_expectation L v hu]
    ring

lemma variance_eq_norm_residual (L : E →L[ℂ] E) (v : E) (hu : ‖v‖=1) :
    variance L v = ‖L v - ⟪v,L v⟫_ℂ • v‖^2 := by
  rw [@norm_sub_sq ℂ,inner_smul_right,← inner_conj_symm (L v) v,
    Complex.mul_conj',norm_smul,hu,mul_one]
  simp only [RCLike.re_eq_complex_re,← Complex.ofReal_pow,Complex.ofReal_re,
    Complex.normSq_eq_norm_sq,variance]
  ring

lemma variance_nonneg (L : E →L[ℂ] E) (v : E) (hu : ‖v‖=1) : 0 ≤ variance L v := by
  rw [variance_eq_norm_residual L v hu]
  positivity

end General

section Scalar
/-- A genuine twice differentiable curve with zero constant and linear terms
has the expected normalized quadratic limit from either side of zero. -/
lemma quadratic_tendsto (f : ℝ → ℝ) (a : ℝ) (hf : ContDiff ℝ 2 f)
    (h0 : f 0=0) (h1 : deriv f 0=0) (h2 : iteratedDeriv 2 f 0=2*a) :
    Filter.Tendsto (fun t => f t/t^2) (𝓝[≠] 0) (𝓝 a) := by
  have hp (t : ℝ) : taylorWithinEval f 2 Set.univ 0 t = a*t^2 := by
    norm_num [taylorWithinEval_succ,taylor_within_zero_eval,
      iteratedDerivWithin_univ,iteratedDeriv_one,h0,h1,h2]
    ring
  have h := taylor_tendsto (f := f) (n := 2) convex_univ (Set.mem_univ 0) hf.contDiffOn
  simp only [nhdsWithin_univ,hp,sub_zero,smul_eq_mul] at h
  have h' : Filter.Tendsto (fun x => (x^2)⁻¹*(f x-a*x^2)) (𝓝[≠] 0) (𝓝 0) :=
    h.mono_left nhdsWithin_le_nhds
  have hs := h'.add (tendsto_const_nhds (x := a))
  simp only [zero_add] at hs
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  field_simp [ht']
end Scalar

section GeneralLimit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem actual_quadratic_limit (L : E →L[ℂ] E) (v : E) (hu : ‖v‖=1) :
    Filter.Tendsto (fun t => actualComplexity L v t/t^2) (𝓝[≠] 0) (𝓝 (variance L v)) := by
  obtain ⟨h0,h1,h2⟩ := actual_initial_data_general L v hu
  exact quadratic_tendsto _ _ (actualComplexity_contDiff L v 2) h0 h1 h2
/-- A stationary seed has a one-dimensional (or zero-dimensional) Krylov
chain, so its actual complexity vanishes for every time. -/
theorem actual_stationary (L : E →L[ℂ] E) (v : E) (c : ℂ) (hv : L v=c • v)
    (t : ℝ) : actualComplexity L v t=0 := by
  have hz : gramSchmidtNormed ℂ (powerSequence L v) 1=0 := by
    apply (KrylovTermination.normed_zero_iff _ _).2
    apply (KrylovTermination.gram_zero_iff_mem _ _).2
    change L v ∈ Submodule.span ℂ (powerSequence L v '' Set.Iio 1)
    rw [hv]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0,by norm_num,by simp [powerSequence]⟩)
  unfold actualComplexity complexity
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.val=0
  · simp [hk]
  · exact (k.property (KrylovTermination.zero_forces_later_zero L v hz (by omega))).elim

lemma actual_zero_variance (L : E →L[ℂ] E) (v : E) (hu : ‖v‖=1)
    (hvar : variance L v=0) (t : ℝ) : actualComplexity L v t=0 := by
  rw [variance_eq_norm_residual L v hu] at hvar
  have hv : L v=⟪v,L v⟫_ℂ • v :=
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hvar))
  exact actual_stationary L v _ hv t

end GeneralLimit

section Matrices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stateGenerator (G : Matrix ι ι ℂ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) G

def stateVariance (G : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℝ :=
  variance (stateGenerator G) (UnitaryEvolution.hilbertVector ψ)

lemma stateGenerator_apply (G : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    stateGenerator G (UnitaryEvolution.hilbertVector ψ) =
      UnitaryEvolution.hilbertVector (G *ᵥ ψ) := rfl

lemma stateGenerator_selfAdjoint (G : Matrix ι ι ℂ) (hG : G.IsHermitian) :
    IsSelfAdjoint (stateGenerator G) :=
  (show IsSelfAdjoint G from hG).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι))

lemma pureSeed_hermitian (ψ : ι → ℂ) : (FactorTwo.pureSeed ψ).IsHermitian := by
  ext i j
  simp [FactorTwo.pureSeed,FactorTwo.outer,Matrix.conjTranspose_apply,mul_comm]

lemma pureVector_unit (ψ : ι → ℂ) (hψ : ‖UnitaryEvolution.hilbertVector ψ‖=1) :
    ‖FactorTwo.rowVectorize (FactorTwo.pureSeed ψ)‖ = 1 := by
  have h := FactorTwoFinite.pure_norm_square_of_unit (UnitaryEvolution.hilbertVector ψ) hψ
  change ‖FactorTwo.rowVectorize (FactorTwo.pureSeed ψ)‖^2=1 at h
  nlinarith [norm_nonneg (FactorTwo.rowVectorize (FactorTwo.pureSeed ψ))]

lemma pure_commutator (G : Matrix ι ι ℂ) (hG : G.IsHermitian) (ψ : ι → ℂ) :
    liouvillian G (FactorTwo.rowVectorize (FactorTwo.pureSeed ψ)) =
      FactorTwo.hilbertOuter (UnitaryEvolution.hilbertVector (G *ᵥ ψ))
        (UnitaryEvolution.hilbertVector ψ) -
      FactorTwo.hilbertOuter (UnitaryEvolution.hilbertVector ψ)
        (UnitaryEvolution.hilbertVector (G *ᵥ ψ)) := by
  rw [liouvillian_rowVectorize,FactorTwo.pureSeed,FactorTwo.mul_outer,
    FactorTwo.outer_mul,hG.eq,map_sub]
  rfl

/-- The squared Hilbert–Schmidt norm of the actual pure-state commutator
is twice the actual energy variance, for an arbitrary mean energy. -/
theorem pure_commutator_norm (G : Matrix ι ι ℂ) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (hψ : ‖UnitaryEvolution.hilbertVector ψ‖=1) :
    ‖liouvillian G (FactorTwo.rowVectorize (FactorTwo.pureSeed ψ))‖^2 =
      2*stateVariance G ψ := by
  let v := UnitaryEvolution.hilbertVector ψ
  let u := UnitaryEvolution.hilbertVector (G *ᵥ ψ)
  have huv : ⟪u,v⟫_ℂ = ⟪v,u⟫_ℂ :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (stateGenerator_selfAdjoint G hG)) v v
  have huu : ⟪u,u⟫_ℂ = ((‖u‖^2 : ℝ) : ℂ) :=
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u).trans (Complex.ofReal_pow ‖u‖ 2).symm
  have hvv : ⟪v,v⟫_ℂ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K,show ‖v‖=1 from hψ]
    norm_num
  rw [pure_commutator G hG ψ]
  change ‖FactorTwo.hilbertOuter u v - FactorTwo.hilbertOuter v u‖^2 =
    2*(‖u‖^2 - ‖⟪v,u⟫_ℂ‖^2)
  rw [@norm_sq_eq_re_inner ℂ,inner_sub_left,inner_sub_right,inner_sub_right]
  simp only [FactorTwo.hilbertOuter_inner]
  simp only [huv,huu,hvv,star_one,mul_one,one_mul,
    Complex.star_def,Complex.conj_ofReal,Complex.mul_conj',
    Complex.normSq_eq_norm_sq,← Complex.ofReal_pow,Complex.sub_re,
    RCLike.re_eq_complex_re,Complex.ofReal_re]
  ring

lemma operator_variance (G : Matrix ι ι ℂ) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (hψ : ‖UnitaryEvolution.hilbertVector ψ‖=1) :
    variance (liouvillian G) (FactorTwo.rowVectorize (FactorTwo.pureSeed ψ)) =
      2*stateVariance G ψ := by
  unfold variance
  rw [seed_commutator_orthogonal G _ (pureSeed_hermitian ψ)]
  simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),sub_zero]
  exact pure_commutator_norm G hG ψ hψ

lemma state_power (G : Matrix ι ι ℂ) (ψ : ι → ℂ) (n : ℕ) :
    ((stateGenerator G)^n) (UnitaryEvolution.hilbertVector ψ) =
      UnitaryEvolution.hilbertVector (G^n *ᵥ ψ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',ContinuousLinearMap.mul_apply,ih,stateGenerator_apply,
      Matrix.mulVec_mulVec,pow_succ']

lemma state_evolution (G : Matrix ι ι ℂ) (ψ : ι → ℂ) (t : ℝ) :
    evolution (skewGenerator (stateGenerator G)) (UnitaryEvolution.hilbertVector ψ) t =
      UnitaryEvolution.evolvedVector G ψ t := by
  letI : SeminormedRing (Matrix ι ι ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  let c : ℂ := -((t:ℂ)*Complex.I)
  have ht : t • skewGenerator (stateGenerator G) = c • stateGenerator G := by
    ext x
    simp [skewGenerator,c,smul_smul,Complex.real_smul,mul_assoc]
  let F : Matrix ι ι ℂ →ₗ[ℂ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    { toFun := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)
      map_add' := map_add (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι))
      map_smul' := fun a A => map_smul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) a A }
  have hc : Continuous (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) :=
    F.continuous_of_finiteDimensional
  have hm := NormedSpace.map_exp ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) hc (c • G)
  simp only [map_smul] at hm
  unfold evolution
  rw [NormedSpace.exp_eq_exp ℝ ℂ,ht]
  change NormedSpace.exp ℂ (c • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) G)
    (UnitaryEvolution.hilbertVector ψ) = _
  rw [← hm]
  rfl

lemma stateComplexity_physical (G : Matrix ι ι ℂ) (ψ : ι → ℂ) (t : ℝ) :
    actualComplexity (stateGenerator G) (UnitaryEvolution.hilbertVector ψ) t =
      complexity (stateSequence G ψ) (UnitaryEvolution.evolvedVector G ψ t) := by
  unfold actualComplexity
  rw [state_evolution]
  congr 1
  funext n
  exact state_power G ψ n

lemma operatorComplexity_physical (G : Matrix ι ι ℂ) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (t : ℝ) :
    actualComplexity (liouvillian G) (FactorTwo.rowVectorize (FactorTwo.pureSeed ψ)) t =
      complexity (operatorSequence G ψ)
        (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector G ψ t)
          (UnitaryEvolution.evolvedVector G ψ t)) := by
  unfold actualComplexity powerSequence
  simp only [liouvillian_power_rowVectorize]
  rw [evolution_rowVectorize G _ hG t]
  congr 1
  simp only [UnitaryCovariance.evolution,Complex.ofReal_neg,neg_mul]
  change FactorTwo.rowVectorize (UnitaryEvolution.propagator G t *
    FactorTwo.pureSeed ψ * (UnitaryEvolution.propagator G t)ᴴ) = _
  rw [← FactorTwoTheorem.pure_conjugation]
  rfl

/-- The physical state complexity has quadratic coefficient Var(G). -/
theorem state_quadratic_limit (G : Matrix ι ι ℂ) (ψ : ι → ℂ)
    (hψ : ‖UnitaryEvolution.hilbertVector ψ‖=1) :
    Filter.Tendsto (fun t =>
      complexity (stateSequence G ψ) (UnitaryEvolution.evolvedVector G ψ t)/t^2)
      (𝓝[≠] 0) (𝓝 (stateVariance G ψ)) := by
  simp_rw [← stateComplexity_physical]
  exact actual_quadratic_limit _ _ hψ

/-- The physical pure-operator complexity has quadratic coefficient
2 Var(G), without a first-moment or spectral nondegeneracy hypothesis. -/
theorem operator_quadratic_limit (G : Matrix ι ι ℂ) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (hψ : ‖UnitaryEvolution.hilbertVector ψ‖=1) :
    Filter.Tendsto (fun t =>
      complexity (operatorSequence G ψ)
        (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector G ψ t)
          (UnitaryEvolution.evolvedVector G ψ t))/t^2)
      (𝓝[≠] 0) (𝓝 (2*stateVariance G ψ)) := by
  simp_rw [← operatorComplexity_physical G hG ψ]
  rw [← operator_variance G hG ψ hψ]
  exact actual_quadratic_limit _ _ (pureVector_unit ψ hψ)

/-- The ratio of the two actual Gram–Schmidt complexities tends to two for
every nonstationary normalized pure seed. -/
theorem pure_ratio_tendsto_two (G : Matrix ι ι ℂ) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (hψ : ‖UnitaryEvolution.hilbertVector ψ‖=1)
    (hvar : 0 < stateVariance G ψ) :
    Filter.Tendsto (fun t =>
      complexity (operatorSequence G ψ)
        (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector G ψ t)
          (UnitaryEvolution.evolvedVector G ψ t)) /
      complexity (stateSequence G ψ) (UnitaryEvolution.evolvedVector G ψ t))
      (𝓝[≠] 0) (𝓝 2) := by
  have h := (operator_quadratic_limit G hG ψ hψ).div
    (state_quadratic_limit G ψ hψ) (ne_of_gt hvar)
  rw [mul_div_cancel_right₀ 2 (ne_of_gt hvar)] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_div_div_cancel_right₀ (pow_ne_zero 2 ht) _ _
/-- Zero energy variance gives zero in both actual physical complexities,
for every real time, including degenerate Hamiltonians. -/
theorem stationary_zero (G : Matrix ι ι ℂ) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (hψ : ‖UnitaryEvolution.hilbertVector ψ‖=1)
    (hvar : stateVariance G ψ=0) (t : ℝ) :
    complexity (stateSequence G ψ) (UnitaryEvolution.evolvedVector G ψ t)=0 ∧
    complexity (operatorSequence G ψ)
      (FactorTwo.hilbertOuter (UnitaryEvolution.evolvedVector G ψ t)
        (UnitaryEvolution.evolvedVector G ψ t))=0 := by
  constructor
  · rw [← stateComplexity_physical]
    exact actual_zero_variance _ _ hψ hvar t
  · rw [← operatorComplexity_physical G hG ψ]
    apply actual_zero_variance _ _ (pureVector_unit ψ hψ)
    rw [operator_variance G hG ψ hψ,hvar,mul_zero]

end Matrices

end
end Krylov.PureShortTime
