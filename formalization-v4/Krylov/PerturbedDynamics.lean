import Krylov.TaylorRemainder
import Krylov.FactorTwoFinite
import Krylov.Perturbation
import Krylov.CyclicEvolution
import Krylov.UnitaryCovariance
import Krylov.KrylovTermination
import Krylov.PurifiedCovariance
import Krylov.PurifiedCurvature

/-! Dynamical infrastructure for actual finite Gram-Schmidt operator chains.
Every number operator below is constructed from the genuine normalized
Gram-Schmidt vectors, retaining the original Krylov degree. -/
namespace Krylov.PerturbedDynamics
open Matrix FactorTwoFinite TaylorRemainder
open scoped InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

section NumberOperator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def numberOperator (f : ℕ → E) : E →L[ℂ] E :=
  ∑ k : GSIndex f, (k.val : ℂ) • ((innerSL ℂ (gsFamily f k)).smulRight (gsFamily f k))

theorem numberOperator_apply (f : ℕ → E) (x : E) :
    numberOperator f x = ∑ k : GSIndex f, ((k.val : ℂ)*⟪gsFamily f k,x⟫_ℂ) • gsFamily f k := by
  simp [numberOperator,ContinuousLinearMap.sum_apply,smul_smul]

theorem numberOperator_expectation (f : ℕ → E) (x : E) :
    (⟪x, numberOperator f x⟫_ℂ).re = complexity f x := by
  rw [numberOperator_apply]
  simp only [inner_sum,inner_smul_right,Complex.re_sum,complexity,probability]
  apply Finset.sum_congr rfl
  intro k _
  rw [← inner_conj_symm x (gsFamily f k),mul_assoc,Complex.mul_conj']
  simp [← Complex.ofReal_pow,← Complex.ofReal_mul]

theorem gs_inner_seed (f : ℕ → E) {k : GSIndex f} (hk : k.val ≠ 0) :
    ⟪gsFamily f k,f 0⟫_ℂ = 0 := by
  simp [gsFamily,gramSchmidtNormed,inner_smul_left,
    gramSchmidt_inv_triangular ℂ f (Nat.pos_of_ne_zero hk)]

theorem numberOperator_seed (f : ℕ → E) : numberOperator f (f 0) = 0 := by
  rw [numberOperator_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.val=0
  · simp [hk]
  · simp [gs_inner_seed f hk]

theorem seed_inner_numberOperator (f : ℕ → E) (x : E) :
    ⟪f 0,numberOperator f x⟫_ℂ = 0 := by
  rw [numberOperator_apply,inner_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.val=0
  · simp [hk]
  · rw [inner_smul_right,← inner_conj_symm (f 0) (gsFamily f k),gs_inner_seed f hk]
    simp

theorem cyclic_reconstruction (f : ℕ → E) (x : E) (hx : x ∈ cyclicSpan f) :
    (∑ k : GSIndex f, ⟪gsFamily f k,x⟫_ℂ • gsFamily f k) = x := by
  classical
  have h := FactorTwo.orthonormal_projection_eq_sum (gsFamily f) (gsFamily_orthonormal f)
    Finset.univ x
  rw [← cyclicSpan_eq f] at h
  simpa [(Submodule.orthogonalProjection_eq_self_iff).mpr hx] using h.symm

theorem gs_inner_first_zero (f : ℕ → E) (horth : ⟪f 0,f 1⟫_ℂ = 0)
    (k : GSIndex f) (hk : k.val ≠ 1) : ⟪gsFamily f k,f 1⟫_ℂ = 0 := by
  by_cases hk0 : k.val=0
  · have hzero : gramSchmidt ℂ f 0 = f 0 := gramSchmidt_zero ℂ f
    simp [gsFamily,gramSchmidtNormed,hk0,hzero,horth]
  · simp [gsFamily,gramSchmidtNormed,inner_smul_left,
      gramSchmidt_inv_triangular ℂ f (show 1 < k.val by omega)]

/-- The actual number operator assigns degree one to the first commutator
when its seed expectation vanishes; no Lanczos recurrence is assumed. -/
theorem numberOperator_first (f : ℕ → E) (horth : ⟪f 0,f 1⟫_ℂ = 0) :
    numberOperator f (f 1) = f 1 := by
  rw [numberOperator_apply]
  calc
    _ = ∑ k : GSIndex f, ⟪gsFamily f k,f 1⟫_ℂ • gsFamily f k := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.val=1
      · simp [hk]
      · simp [gs_inner_first_zero f horth k hk]
    _ = f 1 := cyclic_reconstruction f (f 1) (Submodule.subset_span ⟨1,rfl⟩)

theorem norm_numberOperator_sq (f : ℕ → E) (x : E) :
    ‖numberOperator f x‖^2 = ∑ k : GSIndex f, (k.val : ℝ)^2*‖⟪gsFamily f k,x⟫_ℂ‖^2 := by
  rw [numberOperator_apply,@norm_sq_eq_re_inner ℂ,(gsFamily_orthonormal f).inner_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.normSq_eq_conj_mul_self]
  simp [map_mul,Complex.normSq_eq_norm_sq,norm_mul,mul_pow,←Complex.ofReal_pow,←Complex.ofReal_natCast]

theorem norm_numberOperator_le (f : ℕ → E) {M : ℝ} (hM : 0 ≤ M)
    (hi : ∀ k : GSIndex f, (k.val : ℝ) ≤ M) : ‖numberOperator f‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  have hsq : ‖numberOperator f x‖^2 ≤ (M*‖x‖)^2 := by
    rw [norm_numberOperator_sq]
    calc
      _ ≤ ∑ k : GSIndex f, M^2*‖⟪gsFamily f k,x⟫_ℂ‖^2 := by
        apply Finset.sum_le_sum
        intro k _
        gcongr
        exact hi k
      _ = M^2*∑ k : GSIndex f, ‖⟪gsFamily f k,x⟫_ℂ‖^2 := by rw [Finset.mul_sum]
      _ ≤ M^2*‖x‖^2 := mul_le_mul_of_nonneg_left ((gsFamily_orthonormal f).sum_inner_products_le x) (sq_nonneg M)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp hsq

theorem numberOperator_symmetric (f : ℕ → E) (x y : E) :
    ⟪x,numberOperator f y⟫_ℂ = ⟪numberOperator f x,y⟫_ℂ := by
  simp only [numberOperator_apply,inner_sum,sum_inner,inner_smul_right,inner_smul_left,
    map_mul,map_natCast]
  apply Finset.sum_congr rfl
  intro k _
  rw [← inner_conj_symm x (gsFamily f k)]
  ring_nf

/-- The actual degree operator is selfadjoint. -/
theorem numberOperator_selfAdjoint (f : ℕ → E) : IsSelfAdjoint (numberOperator f) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact (numberOperator_symmetric f x y).symm

def powerSequence (L : E →L[ℂ] E) (v : E) (n : ℕ) : E := (L^n) v

def skewGenerator (L : E →L[ℂ] E) : E →L[ℂ] E := (-Complex.I) • L

def actualComplexity (L : E →L[ℂ] E) (v : E) (t : ℝ) : ℝ :=
  complexity (powerSequence L v) (evolution (skewGenerator L) v t)

theorem actualComplexity_eq_expectation (L : E →L[ℂ] E) (v : E) :
    actualComplexity L v = expectation (skewGenerator L) (numberOperator (powerSequence L v)) v := by
  funext t
  exact (numberOperator_expectation _ _).symm

theorem actualComplexity_contDiff (L : E →L[ℂ] E) (v : E) (n : ℕ) :
    ContDiff ℝ n (actualComplexity L v) := by
  rw [actualComplexity_eq_expectation]
  exact expectation_contDiff _ _ _ n

theorem actual_initial_data (L : E →L[ℂ] E) (v : E) (horth : ⟪v,L v⟫_ℂ=0) :
    actualComplexity L v 0 = 0 ∧ deriv (actualComplexity L v) 0 = 0 ∧
      iteratedDeriv 2 (actualComplexity L v) 0 = 2*‖L v‖^2 := by
  rw [actualComplexity_eq_expectation]
  have hN : numberOperator (powerSequence L v) v=0 := by
    simpa [powerSequence] using numberOperator_seed (powerSequence L v)
  have hleft : ∀ x, ⟪v,numberOperator (powerSequence L v) x⟫_ℂ=0 := by
    intro x
    simpa [powerSequence] using seed_inner_numberOperator (powerSequence L v) x
  have hvel : numberOperator (powerSequence L v) (skewGenerator L v)=skewGenerator L v := by
    have h1 := numberOperator_first (powerSequence L v) (by simpa [powerSequence] using horth)
    simpa [powerSequence,skewGenerator] using congrArg (fun x : E => (-Complex.I) • x) h1
  have h := expectation_initial_data (skewGenerator L) (numberOperator (powerSequence L v)) v hN hleft hvel
  simpa [skewGenerator,norm_smul] using h

theorem skewGenerator_skewAdjoint (L : E →L[ℂ] E) (hL : IsSelfAdjoint L) :
    skewGenerator L ∈ skewAdjoint (E →L[ℂ] E) := by
  exact IsSelfAdjoint.smul_mem_skewAdjoint (by simp [skewAdjoint.mem_iff,Complex.star_def]) hL

theorem evolution_norm (L : E →L[ℂ] E) (hL : IsSelfAdjoint L) (v : E) (t : ℝ) :
    ‖evolution (skewGenerator L) v t‖ = ‖v‖ := by
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ
  have hs := skewGenerator_skewAdjoint L hL
  rw [skewAdjoint.mem_iff] at hs ⊢
  simp [star_smul,hs]

theorem actual_third_zero (L : E →L[ℂ] E) (hL : IsSelfAdjoint L) (v : E)
    (horth : ⟪v,L v⟫_ℂ=0) : iteratedDeriv 3 (actualComplexity L v) 0=0 := by
  rw [actualComplexity_eq_expectation]
  apply expectation_third_zero
  · exact skewAdjoint.mem_iff.mp (skewGenerator_skewAdjoint L hL)
  · simpa [powerSequence] using numberOperator_seed (powerSequence L v)
  · intro x
    simpa [powerSequence] using seed_inner_numberOperator (powerSequence L v) x
  · exact numberOperator_symmetric _
  · have h1 := numberOperator_first (powerSequence L v) (by simpa [powerSequence] using horth)
    simpa [powerSequence,skewGenerator] using congrArg (fun x : E => (-Complex.I) • x) h1

theorem actual_quartic_remainder (L : E →L[ℂ] E) (hL : IsSelfAdjoint L)
    (v : E) (hunit : ‖v‖=1) (horth : ⟪v,L v⟫_ℂ=0) {t : ℝ} (ht : 0<t) :
    |actualComplexity L v t-‖L v‖^2*t^2| ≤
      ((2*‖L‖)^4*‖numberOperator (powerSequence L v)‖)*t^4/24 := by
  obtain ⟨h0,h1,h2⟩ := actual_initial_data L v horth
  apply quartic_remainder ht (actualComplexity_contDiff L v 4) h0 h1 h2
    (actual_third_zero L hL v horth)
  intro x _
  rw [actualComplexity_eq_expectation]
  have h := abs_iteratedDeriv_le (skewGenerator L) (numberOperator (powerSequence L v)) v 4 x
    (by rw [evolution_norm L hL,hunit])
  simpa [skewGenerator,norm_smul] using h

theorem numberOperator_norm_le_finrank (L : E →L[ℂ] E) (v : E) :
    ‖numberOperator (powerSequence L v)‖ ≤ (Module.finrank ℂ E : ℝ) := by
  apply norm_numberOperator_le _ (Nat.cast_nonneg _)
  intro k
  exact_mod_cast (KrylovTermination.active_index_lt_finrank L v k).le

end NumberOperator
section Matrices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix of the actual commutator in row-vectorized Hilbert--Schmidt coordinates. -/
def commutatorMatrix (G : Matrix ι ι ℂ) : Matrix (ι×ι) (ι×ι) ℂ :=
  fun a b => G a.1 b.1 * (if a.2=b.2 then 1 else 0) -
    (if a.1=b.1 then 1 else 0)*G b.2 a.2

def liouvillian (G : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι×ι) →L[ℂ] EuclideanSpace ℂ (ι×ι) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι×ι)) (commutatorMatrix G)

theorem liouvillian_rowVectorize (G X : Matrix ι ι ℂ) :
    liouvillian G (FactorTwo.rowVectorize X) = FactorTwo.rowVectorize (G*X-X*G) := by
  apply (WithLp.equiv 2 ((ι×ι) → ℂ)).injective
  ext ⟨i,j⟩
  change (∑ b : ι×ι,commutatorMatrix G (i,j) b * X b.1 b.2) = (G*X-X*G) i j
  simp [commutatorMatrix,Matrix.mul_apply,Fintype.sum_prod_type,
    Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul,sub_mul,mul_sub,ite_mul,mul_ite]
  simp [mul_comm]

theorem commutatorMatrix_hermitian (G : Matrix ι ι ℂ) (hG : G.IsHermitian) :
    (commutatorMatrix G).IsHermitian := by
  ext ⟨i,j⟩ ⟨k,l⟩
  have hg (a b : ι) : star (G b a)=G a b := congrFun (congrFun hG a) b
  by_cases hik : i=k <;> by_cases hjl : j=l <;>
    simp [commutatorMatrix,Matrix.conjTranspose_apply,hg,hik,hjl,eq_comm]

theorem liouvillian_selfAdjoint (G : Matrix ι ι ℂ) (hG : G.IsHermitian) :
    IsSelfAdjoint (liouvillian G) := by
  exact (show IsSelfAdjoint (commutatorMatrix G) from commutatorMatrix_hermitian G hG).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι×ι))

/-- A selfadjoint seed is orthogonal to its actual matrix commutator. -/
theorem seed_commutator_orthogonal (G X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    ⟪FactorTwo.rowVectorize X,liouvillian G (FactorTwo.rowVectorize X)⟫_ℂ = 0 := by
  rw [liouvillian_rowVectorize,FactorTwo.rowVectorize_inner]
  change OperatorBridge.hsInner X (G*X-X*G)=0
  rw [UnitaryCovariance.hsInner_eq_trace,hX.eq,Matrix.mul_sub,Matrix.trace_sub]
  rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle]
  simp [Matrix.mul_assoc]

theorem norm_toEuclideanCLM_le_frobenius (B : Matrix ι ι ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hB : ∑ i,∑ j,‖B i j‖^2 ≤ R^2) : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) B‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  have hsq : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) B x‖^2 ≤ (R*‖x‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ i, (∑ j, ‖B i j‖^2)*‖x‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        change ‖∑ j, B i j*x j‖^2 ≤ _
        calc
          _ ≤ (∑ j,‖B i j‖*‖x j‖)^2 := by
            gcongr
            simpa [norm_mul] using (norm_sum_le (Finset.univ : Finset ι) (fun j => B i j*x j))
          _ ≤ (∑ j,‖B i j‖^2)*(∑ j,‖x j‖^2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
          _ = _ := by rw [PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) x]
      _ = (∑ i,∑ j,‖B i j‖^2)*‖x‖^2 := by rw [Finset.sum_mul]
      _ ≤ R^2*‖x‖^2 := mul_le_mul_of_nonneg_right hB (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg _))).mp hsq

theorem rowVectorize_norm_sq (X : Matrix ι ι ℂ) :
    ‖FactorTwo.rowVectorize X‖^2 = ∑ i,∑ j,Complex.normSq (X i j) := by
  rw [@norm_sq_eq_re_inner ℂ,FactorTwo.rowVectorize_inner]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self]
  rfl

theorem commutatorMatrix_normSq_entry (G : Matrix ι ι ℂ) (hd : ∀ i,G i i=0)
    (a b : ι×ι) :
    Complex.normSq (commutatorMatrix G a b) =
      (if a.2=b.2 then Complex.normSq (G a.1 b.1) else 0) +
      (if a.1=b.1 then Complex.normSq (G b.2 a.2) else 0) := by
  rcases a with ⟨i,j⟩; rcases b with ⟨k,l⟩
  by_cases hik : i=k <;> by_cases hjl : j=l
  · subst k; subst l; simp [commutatorMatrix,hd]
  · subst k; simp [commutatorMatrix,hd,hjl]
  · subst l; simp [commutatorMatrix,hd,hik]
  · simp [commutatorMatrix,hik,hjl]

/-- A direct finite entry calculation gives the Hilbert--Schmidt norm of the
commutator matrix for any zero-diagonal generator. -/
theorem commutatorMatrix_frobenius (G : Matrix ι ι ℂ) (hd : ∀ i,G i i=0) :
    (∑ a : ι×ι,∑ b : ι×ι,Complex.normSq (commutatorMatrix G a b)) =
      2*(Fintype.card ι : ℝ)*(∑ i,∑ j,Complex.normSq (G i j)) := by
  simp_rw [commutatorMatrix_normSq_entry G hd]
  simp only [Finset.sum_add_distrib,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  have hh : (∑ i : ι,∑ j : ι,∑ k : ι,∑ l : ι,if i=k then Complex.normSq (G l j) else 0) =
      (Fintype.card ι : ℝ)*(∑ i,∑ j,Complex.normSq (G i j)) := by
    calc
      _ = ∑ i : ι,∑ j : ι,∑ l : ι,∑ k : ι,if i=k then Complex.normSq (G l j) else 0 := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        exact Finset.sum_comm
      _ = (Fintype.card ι : ℝ)*(∑ j,∑ l,Complex.normSq (G l j)) := by simp
      _ = _ := by rw [Finset.sum_comm]
  rw [hh]
  ring_nf

theorem liouvillian_power_rowVectorize (G X : Matrix ι ι ℂ) (n : ℕ) :
    (liouvillian G ^ n) (FactorTwo.rowVectorize X) =
      FactorTwo.rowVectorize ((FactorTwo.commutator G ^ n) X) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ',ContinuousLinearMap.mul_apply,Module.End.mul_apply,ih,
      liouvillian_rowVectorize,FactorTwo.commutator_apply]

/-- The vector curve used in the actual complexity is precisely normalized
matrix unitary conjugation, through the actual commutator exponential. -/
theorem evolution_rowVectorize (G X : Matrix ι ι ℂ) (hG : G.IsHermitian) (t : ℝ) :
    evolution (skewGenerator (liouvillian G)) (FactorTwo.rowVectorize X) t =
      FactorTwo.rowVectorize (UnitaryCovariance.evolution G X t) := by
  letI : SeminormedRing (Matrix ι ι ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  let T : Matrix ι ι ℂ →L[ℂ] EuclideanSpace ℂ (ι×ι) :=
    (FactorTwo.rowVectorize (ι := ι)).toContinuousLinearEquiv.toContinuousLinearMap
  let c : ℂ := ((-t : ℝ) : ℂ)*Complex.I
  have ht : t • skewGenerator (liouvillian G) = c • liouvillian G := by
    ext x
    simp [skewGenerator,c,smul_smul,Complex.real_smul,mul_assoc]
  have hh := exponential_intertwining T (CyclicEvolution.ad G) (liouvillian G)
    (fun Y => by simpa [T,CyclicEvolution.ad_apply] using (liouvillian_rowVectorize G Y).symm) X c
  rw [CyclicEvolution.exp_ad_apply] at hh
  change FactorTwo.rowVectorize (NormedSpace.exp ℂ (c • G)*X*NormedSpace.exp ℂ ((-c) • G)) =
    NormedSpace.exp ℂ (c • liouvillian G) (FactorTwo.rowVectorize X) at hh
  unfold evolution
  rw [NormedSpace.exp_eq_exp ℝ ℂ,ht,← hh]
  change FactorTwo.rowVectorize _=FactorTwo.rowVectorize _
  apply congrArg FactorTwo.rowVectorize
  unfold UnitaryCovariance.evolution
  change NormedSpace.exp ℂ (c • G)*X*NormedSpace.exp ℂ ((-c) • G) =
    NormedSpace.exp ℂ (c • G)*X*(NormedSpace.exp ℂ (c • G))ᴴ
  rw [← Matrix.exp_conjTranspose]
  congr 2
  simp [Matrix.conjTranspose_smul,hG.eq,c,Complex.star_def]

end Matrices
section Qutrit

def complexHamiltonian (δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (Perturbation.hamiltonian δ).map Complex.ofReal

def mixedSeed : Matrix (Fin 3) (Fin 3) ℂ := States.rhoR.map Complex.ofReal

def mixedVector : EuclideanSpace ℂ (Fin 3×Fin 3) :=
  (Real.sqrt 2 : ℂ) • FactorTwo.rowVectorize mixedSeed

def purifiedGenerator (δ : ℝ) : Matrix (Fin 3×Fin 3) (Fin 3×Fin 3) ℂ :=
  PurifiedCovariance.lift (complexHamiltonian δ)

def purifiedVector : EuclideanSpace ℂ ((Fin 3×Fin 3)×(Fin 3×Fin 3)) :=
  FactorTwo.rowVectorize PurifiedCovariance.originalSeed

def mixedComplexity (δ t : ℝ) : ℝ := actualComplexity (liouvillian (complexHamiltonian δ)) mixedVector t

def purifiedComplexity (δ t : ℝ) : ℝ := actualComplexity (liouvillian (purifiedGenerator δ)) purifiedVector t

theorem complexHamiltonian_hermitian (δ : ℝ) : (complexHamiltonian δ).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexHamiltonian,Perturbation.hamiltonian,conjTranspose_apply]

theorem purifiedGenerator_hermitian (δ : ℝ) : (purifiedGenerator δ).IsHermitian := by
  change (PurifiedCovariance.lift (complexHamiltonian δ))ᴴ=PurifiedCovariance.lift (complexHamiltonian δ)
  rw [PurifiedCovariance.lift_adjoint,(complexHamiltonian_hermitian δ).eq]

theorem mixedSeed_hermitian : mixedSeed.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [mixedSeed,States.rhoR,conjTranspose_apply,Matrix.diagonal]

theorem mixedSeed_norm_sq : ‖FactorTwo.rowVectorize mixedSeed‖^2=1/2 := by
  rw [rowVectorize_norm_sq]
  norm_num [mixedSeed,States.rhoR,Fin.sum_univ_succ,Matrix.diagonal,Complex.normSq_ofReal]

theorem mixedVector_unit : ‖mixedVector‖=1 := by
  have hn : ‖mixedVector‖^2=1 := by
    rw [mixedVector,norm_smul,mul_pow,mixedSeed_norm_sq]
    simp [Complex.norm_real,abs_of_nonneg (Real.sqrt_nonneg 2),Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [norm_nonneg mixedVector]

theorem mixedVector_orthogonal (δ : ℝ) :
    ⟪mixedVector,liouvillian (complexHamiltonian δ) mixedVector⟫_ℂ=0 := by
  simp [mixedVector,map_smul,inner_smul_left,inner_smul_right,
    seed_commutator_orthogonal _ _ mixedSeed_hermitian]

theorem complexHamiltonian_diagonal (δ : ℝ) (i : Fin 3) : complexHamiltonian δ i i=0 := by
  fin_cases i <;> simp [complexHamiltonian,Perturbation.hamiltonian]

theorem purifiedGenerator_diagonal (δ : ℝ) (a : Fin 3×Fin 3) : purifiedGenerator δ a a=0 := by
  simp [purifiedGenerator,PurifiedCovariance.lift,Matrix.kronecker_apply,complexHamiltonian_diagonal]

theorem complexHamiltonian_frobenius (δ : ℝ) :
    (∑ i,∑ j,Complex.normSq (complexHamiltonian δ i j))=2+10*δ^2 := by
  norm_num [complexHamiltonian,Perturbation.hamiltonian,Fin.sum_univ_succ,Complex.normSq_ofReal]
  ring_nf

theorem purifiedGenerator_frobenius (δ : ℝ) :
    (∑ a,∑ b,Complex.normSq (purifiedGenerator δ a b))=3*(2+10*δ^2) := by
  simp only [purifiedGenerator,PurifiedCovariance.lift,Matrix.kronecker_apply,
    Fintype.sum_prod_type,Matrix.one_apply,mul_ite,mul_one,mul_zero,apply_ite,
    map_zero,Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,if_true,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  rw [complexHamiltonian_frobenius]
  rfl

theorem mixed_liouvillian_bound : ‖liouvillian (complexHamiltonian (1/20))‖ ≤ 12 := by
  apply norm_toEuclideanCLM_le_frobenius _ (by norm_num)
  simp_rw [← Complex.normSq_eq_norm_sq]
  rw [commutatorMatrix_frobenius _ (complexHamiltonian_diagonal _),complexHamiltonian_frobenius]
  norm_num

theorem purified_liouvillian_bound : ‖liouvillian (purifiedGenerator (1/20))‖ ≤ 12 := by
  apply norm_toEuclideanCLM_le_frobenius _ (by norm_num)
  simp_rw [← Complex.normSq_eq_norm_sq]
  rw [commutatorMatrix_frobenius _ (purifiedGenerator_diagonal _),purifiedGenerator_frobenius]
  norm_num

theorem mixed_curvature (δ : ℝ) :
    ‖liouvillian (complexHamiltonian δ) mixedVector‖^2 = Perturbation.mixedCurvature δ := by
  have hc : complexHamiltonian δ*mixedSeed-mixedSeed*complexHamiltonian δ =
      (Perturbation.hamiltonian δ*States.rhoR-States.rhoR*Perturbation.hamiltonian δ).map Complex.ofReal := by
    unfold complexHamiltonian mixedSeed
    rw [← UnitaryCovariance.complexify_mul,← UnitaryCovariance.complexify_mul]
    ext i j
    simp
  rw [mixedVector,map_smul,norm_smul,mul_pow,liouvillian_rowVectorize,hc,rowVectorize_norm_sq]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg 2),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Matrix.map_apply,Complex.normSq_ofReal]
  unfold Perturbation.mixedCurvature States.hsNormSq
  rw [States.rhoR_purity]
  ring_nf

theorem purifiedSeed_hermitian : PurifiedCovariance.originalSeed.IsHermitian := by
  rw [← PurifiedCurvature.seed_eq]
  ext a b
  simp [FactorTwo.pureSeed,FactorTwo.outer,Matrix.conjTranspose_apply,mul_comm]

theorem purifiedVector_unit : ‖purifiedVector‖=1 := by
  have hn : ‖purifiedVector‖^2=1 := by
    rw [purifiedVector,@norm_sq_eq_re_inner ℂ,FactorTwo.rowVectorize_inner]
    change (OperatorBridge.hsInner PurifiedCovariance.originalSeed PurifiedCovariance.originalSeed).re=1
    rw [PurifiedCurvature.seed_hs_norm]
    rfl
  nlinarith [norm_nonneg purifiedVector]

theorem purifiedVector_orthogonal (δ : ℝ) :
    ⟪purifiedVector,liouvillian (purifiedGenerator δ) purifiedVector⟫_ℂ=0 :=
  seed_commutator_orthogonal _ _ purifiedSeed_hermitian

theorem purified_curvature (δ : ℝ) :
    ‖liouvillian (purifiedGenerator δ) purifiedVector‖^2 = Perturbation.purifiedCurvature δ := by
  rw [purifiedVector,liouvillian_rowVectorize,@norm_sq_eq_re_inner ℂ,FactorTwo.rowVectorize_inner]
  change (OperatorBridge.hsInner
    (FactorTwo.commutator (PurifiedCurvature.generator δ) PurifiedCovariance.originalSeed)
    (FactorTwo.commutator (PurifiedCurvature.generator δ) PurifiedCovariance.originalSeed)).re = _
  rw [PurifiedCurvature.commutator_hs_norm]
  norm_num [←Complex.ofReal_pow,Perturbation.purifiedCurvature,States.rhoR,Perturbation.hamiltonian,
    Matrix.trace,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]
  ring_nf

theorem mixed_number_bound (δ : ℝ) :
    ‖numberOperator (powerSequence (liouvillian (complexHamiltonian δ)) mixedVector)‖ ≤ 81 := by
  have h := numberOperator_norm_le_finrank (liouvillian (complexHamiltonian δ)) mixedVector
  norm_num at h
  linarith

theorem purified_number_bound (δ : ℝ) :
    ‖numberOperator (powerSequence (liouvillian (purifiedGenerator δ)) purifiedVector)‖ ≤ 81 := by
  have h := numberOperator_norm_le_finrank (liouvillian (purifiedGenerator δ)) purifiedVector
  norm_num at h
  exact h

theorem mixed_finite_remainder {t : ℝ} (ht : 0<t) :
    |mixedComplexity (1/20) t-Perturbation.mixedCurvature (1/20)*t^2| ≤ 1119744*t^4 := by
  have h := actual_quartic_remainder (liouvillian (complexHamiltonian (1/20)))
    (liouvillian_selfAdjoint _ (complexHamiltonian_hermitian _)) mixedVector mixedVector_unit
    (mixedVector_orthogonal _) ht
  rw [mixed_curvature] at h
  apply h.trans
  have hl := mixed_liouvillian_bound
  have hn := mixed_number_bound (1/20)
  calc
    _ ≤ ((2*(12:ℝ))^4*81)*t^4/24 := by gcongr
    _ = _ := by ring

theorem purified_finite_remainder {t : ℝ} (ht : 0<t) :
    |purifiedComplexity (1/20) t-Perturbation.purifiedCurvature (1/20)*t^2| ≤ 1119744*t^4 := by
  have h := actual_quartic_remainder (liouvillian (purifiedGenerator (1/20)))
    (liouvillian_selfAdjoint _ (purifiedGenerator_hermitian _)) purifiedVector purifiedVector_unit
    (purifiedVector_orthogonal _) ht
  rw [purified_curvature] at h
  apply h.trans
  have hl := purified_liouvillian_bound
  have hn := purified_number_bound (1/20)
  calc
    _ ≤ ((2*(12:ℝ))^4*81)*t^4/24 := by gcongr
    _ = _ := by ring

/-- The requested rational certificate follows from a stronger fourth-order
remainder for the actual Gram-Schmidt commutator dynamics. -/
theorem perturbed_finite_lower_bound :
    (378247/21125000000000000 : ℝ) ≤
      mixedComplexity (1/20) (1/20000)-purifiedComplexity (1/20) (1/20000) := by
  have hm := (abs_le.mp (mixed_finite_remainder (t := 1/20000) (by norm_num))).1
  have hp := (abs_le.mp (purified_finite_remainder (t := 1/20000) (by norm_num))).2
  have hc := Perturbation.curvature_finite
  nlinarith

theorem perturbed_finite_violation :
    purifiedComplexity (1/20) (1/20000) < mixedComplexity (1/20) (1/20000) := by
  have h := perturbed_finite_lower_bound
  linarith

/-- Every parameter in the source curvature range has a genuine open
positive-time interval of strict upper-side violation. -/
theorem perturbed_small_time_violation {δ : ℝ} (hδ : δ^2<1/135) :
    ∃ ε>0, ∀ t : ℝ, 0<t → t<ε → purifiedComplexity δ t < mixedComplexity δ t := by
  let LM := liouvillian (complexHamiltonian δ)
  let LP := liouvillian (purifiedGenerator δ)
  let BM : ℝ := (2*‖LM‖)^4*‖numberOperator (powerSequence LM mixedVector)‖/24
  let BP : ℝ := (2*‖LP‖)^4*‖numberOperator (powerSequence LP purifiedVector)‖/24
  have hB : 0≤BM+BP := by dsimp [BM,BP]; positivity
  have hk : 0<Perturbation.mixedCurvature δ-Perturbation.purifiedCurvature δ :=
    sub_pos.mpr (Perturbation.curvature_gap_positive hδ)
  obtain ⟨ε,hε,hpol⟩ := positive_quadratic_minus_quartic hk hB
  refine ⟨ε,hε,?_⟩
  intro t ht hte
  have hm := actual_quartic_remainder LM
    (liouvillian_selfAdjoint _ (complexHamiltonian_hermitian _)) mixedVector mixedVector_unit
    (mixedVector_orthogonal δ) ht
  have hp := actual_quartic_remainder LP
    (liouvillian_selfAdjoint _ (purifiedGenerator_hermitian _)) purifiedVector purifiedVector_unit
    (purifiedVector_orthogonal δ) ht
  have hm' : |mixedComplexity δ t-Perturbation.mixedCurvature δ*t^2| ≤ BM*t^4 := by
    simpa only [LM,mixed_curvature,mixedComplexity,BM,div_mul_eq_mul_div] using hm
  have hp' : |purifiedComplexity δ t-Perturbation.purifiedCurvature δ*t^2| ≤ BP*t^4 := by
    simpa only [LP,purified_curvature,purifiedComplexity,BP,div_mul_eq_mul_div] using hp
  have hl := (abs_le.mp hm').1
  have hu := (abs_le.mp hp').2
  have hpos := hpol t ht hte
  nlinarith

/-- The displayed source interval gives both irreducibility and actual
strict short-time violation, with no conditional dynamical hypotheses. -/
theorem robust_qutrit_witness {δ : ℝ} (hδ0 : 0 < |δ|) (hδ : |δ| < 1/Real.sqrt 135) :
    (∀ P : Matrix (Fin 3) (Fin 3) ℂ,
      P*P=P → P*mixedSeed=mixedSeed*P →
      P*complexHamiltonian δ=complexHamiltonian δ*P → P=0 ∨ P=1) ∧
    (∃ ε>0, ∀ t : ℝ, 0<t → t<ε → purifiedComplexity δ t < mixedComplexity δ t) := by
  have hne : δ≠0 := abs_pos.mp hδ0
  have hs : 0<Real.sqrt 135 := Real.sqrt_pos.mpr (by norm_num)
  have hm : |δ| *Real.sqrt 135 < 1 := (lt_div_iff₀ hs).mp hδ
  have hz : 0 ≤ |δ| *Real.sqrt 135 := mul_nonneg (abs_nonneg δ) hs.le
  have hsq : (|δ| *Real.sqrt 135)^2<1 := by nlinarith
  rw [mul_pow,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 135)] at hsq
  have hδsq : δ^2<1/135 := by nlinarith
  constructor
  · intro P hP hρ hH
    exact Perturbation.no_common_nontrivial_idempotent hne P hP hρ hH
  · exact perturbed_small_time_violation hδsq

/-- Unfolded physical meaning of the mixed witness: normalized initial
Hilbert--Schmidt seed, true commutator powers, and true unitary conjugation. -/
theorem mixedComplexity_physical (δ t : ℝ) :
    mixedComplexity δ t = complexity
      (fun n => (Real.sqrt 2 : ℂ) • FactorTwo.rowVectorize
        ((FactorTwo.commutator (complexHamiltonian δ)^n) mixedSeed))
      ((Real.sqrt 2 : ℂ) • FactorTwo.rowVectorize
        (UnitaryCovariance.evolution (complexHamiltonian δ) mixedSeed t)) := by
  unfold mixedComplexity actualComplexity powerSequence mixedVector
  simp only [map_smul,liouvillian_power_rowVectorize]
  congr 1
  change (NormedSpace.exp ℝ (t • skewGenerator (liouvillian (complexHamiltonian δ))))
    ((Real.sqrt 2 : ℂ) • FactorTwo.rowVectorize mixedSeed) = _
  rw [map_smul]
  congr 1
  exact evolution_rowVectorize _ _ (complexHamiltonian_hermitian δ) t

/-- The purified witness is the actual rank-one canonical-purification
operator chain under H_delta tensor I. -/
theorem purifiedComplexity_physical (δ t : ℝ) :
    purifiedComplexity δ t = complexity
      (fun n => FactorTwo.rowVectorize ((FactorTwo.commutator (purifiedGenerator δ)^n)
        PurifiedCovariance.originalSeed))
      (FactorTwo.rowVectorize (UnitaryCovariance.evolution (purifiedGenerator δ)
        PurifiedCovariance.originalSeed t)) := by
  unfold purifiedComplexity actualComplexity powerSequence purifiedVector
  simp only [liouvillian_power_rowVectorize]
  rw [evolution_rowVectorize _ _ (purifiedGenerator_hermitian δ)]

end Qutrit
end
end Krylov.PerturbedDynamics
