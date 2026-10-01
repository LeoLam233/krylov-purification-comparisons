import Krylov.FactorTwoTheorem
import Krylov.OperatorBridge

/-! Real spectral polynomials for the actual complex-seed Gram–Schmidt
construction, and its literal matrix-exponential spectral amplitude. -/
namespace Krylov.PhysicalSpectralPolynomials
open Matrix
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

section Isometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Unitary coordinate transport commutes with the actual unnormalized
Gram–Schmidt process, including all terminating zeros. -/
theorem isometry_gramSchmidt (T : E ≃ₗᵢ[ℂ] F) (f : ℕ → E) (n : ℕ) :
    T (gramSchmidt ℂ f n) = gramSchmidt ℂ (fun k => T (f k)) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [gramSchmidt_def ℂ f n,gramSchmidt_def ℂ (fun k => T (f k)) n,map_sub,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Submodule.orthogonalProjection_singleton,
      Submodule.orthogonalProjection_singleton,← ih i (Finset.mem_Iio.mp hi),map_smul,
      T.inner_map_map,T.norm_map]

/-- Normalization commutes with the same unitary coordinate transport. -/
theorem isometry_gramSchmidtNormed (T : E ≃ₗᵢ[ℂ] F) (f : ℕ → E) (n : ℕ) :
    T (gramSchmidtNormed ℂ f n) = gramSchmidtNormed ℂ (fun k => T (f k)) n := by
  simp only [gramSchmidtNormed,map_smul,← isometry_gramSchmidt T f n,T.norm_map]

/-- The source's Lanczos phase convention does not affect any probability. -/
theorem phase_probability (c : ℂ) (hc : ‖c‖=1) (x y : E) :
    ‖⟪c • x,y⟫_ℂ‖^2 = ‖⟪x,y⟫_ℂ‖^2 := by
  rw [inner_smul_left,norm_mul]
  simp [hc]
end Isometry

section Diagonal
variable {ι : Type*} [Fintype ι]

/-- A real polynomial applied to a diagonal real generator and an arbitrary
complex seed, with its original coordinate phases retained. -/
def polynomialMap (e : ι → ℝ) (v : ι → ℂ) :
    Polynomial ℝ →ₗ[ℝ] EuclideanSpace ℂ ι where
  toFun p := (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm (fun i => ((p.eval (e i) : ℝ) : ℂ)*v i)
  map_add' p q := by
    ext i
    simp [Polynomial.eval_add,add_mul]
  map_smul' c p := by
    ext i
    simp [Polynomial.smul_eq_C_mul,Polynomial.eval_C_mul,Complex.real_smul,mul_assoc]

@[simp] lemma polynomialMap_apply (e : ι → ℝ) (v : ι → ℂ) (p : Polynomial ℝ) (i : ι) :
    polynomialMap e v p i = ((p.eval (e i) : ℝ) : ℂ)*v i := rfl

def powers (e : ι → ℝ) (v : ι → ℂ) (n : ℕ) : EuclideanSpace ℂ ι :=
  polynomialMap e v (Polynomial.X^n)

@[simp] lemma powers_apply (e : ι → ℝ) (v : ι → ℂ) (n : ℕ) (i : ι) :
    powers e v n i = (e i : ℂ)^n*v i := by
  simp [powers]

def weightedDot (e : ι → ℝ) (v : ι → ℂ) (p q : Polynomial ℝ) : ℝ :=
  ∑ i, ‖v i‖^2*p.eval (e i)*q.eval (e i)

/-- Inner products of real polynomial vectors are real even when the seed
coordinates have arbitrary complex phases. -/
lemma polynomial_inner (e : ι → ℝ) (v : ι → ℂ) (p q : Polynomial ℝ) :
    ⟪polynomialMap e v p,polynomialMap e v q⟫_ℂ = (weightedDot e v p q : ℂ) := by
  rw [PiLp.inner_apply]
  unfold weightedDot
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp only [polynomialMap_apply,RCLike.inner_apply,map_mul,
    RCLike.conj_ofReal,Complex.conj_ofReal]
  have h : v i * star (v i) = (‖v i‖^2 : ℝ) := by
    simpa [Complex.star_def,Complex.normSq_eq_norm_sq] using Complex.mul_conj' (v i)
  change ((q.eval (e i) : ℝ) : ℂ)*v i*(((p.eval (e i) : ℝ) : ℂ)*star (v i)) = _
  calc
    _ = (((p.eval (e i) : ℝ) : ℂ)*((q.eval (e i) : ℝ) : ℂ))*(v i*star (v i)) := by ring
    _ = _ := by rw [h]; push_cast; ring

/-- Projection between real polynomial vectors again uses a real scalar.
This is stated independently of the recursive choice of previous polynomials. -/
lemma polynomial_projection (e : ι → ℝ) (v : ι → ℂ) (p q : Polynomial ℝ) :
    ((ℂ ∙ polynomialMap e v p).orthogonalProjection (polynomialMap e v q) :
      EuclideanSpace ℂ ι) =
      polynomialMap e v ((weightedDot e v p q / ‖polynomialMap e v p‖^2) • p) := by
  rw [Submodule.orthogonalProjection_singleton,polynomial_inner e v p q]
  ext i
  simp only [PiLp.smul_apply,polynomialMap_apply,Polynomial.smul_eq_C_mul,
    Polynomial.eval_C_mul,smul_eq_mul]
  push_cast
  simp only [RCLike.ofReal,Algebra.cast,Complex.coe_algebraMap]
  ring

/-- The raw complex Gram–Schmidt vectors have real polynomial representatives
without first replacing the complex seed by a square-root-weight model. -/
theorem raw_monic_polynomial (e : ι → ℝ) (v : ι → ℂ) (n : ℕ) :
    ∃ p : Polynomial ℝ, p.Monic ∧ p.degree = (n : WithBot ℕ) ∧
      gramSchmidt ℂ (powers e v) n = polynomialMap e v p := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    choose p hm hd hp using fun j : Fin n => ih j.val j.isLt
    let c : Fin n → ℝ := fun j =>
      weightedDot e v (p j) (Polynomial.X^n) / ‖gramSchmidt ℂ (powers e v) j.val‖^2
    have hdegree : (∑ j : Fin n, c j • p j).degree < (n : WithBot ℕ) := by
      apply (Polynomial.degree_sum_le _ _).trans_lt
      apply (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2
      intro j _
      apply (Polynomial.degree_smul_le (c j) (p j)).trans_lt
      rw [hd j]
      exact WithBot.coe_lt_coe.mpr j.isLt
    refine ⟨Polynomial.X^n - ∑ j : Fin n, c j • p j,
      Polynomial.monic_X_pow_sub hdegree, ?_, ?_⟩
    · have hlt : (∑ j : Fin n, c j • p j).degree < (Polynomial.X^n : Polynomial ℝ).degree := by
        simpa using hdegree
      rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt]
      simp
    rw [gramSchmidt_def,Nat.Iio_eq_range,← Fin.sum_univ_eq_sum_range,
      map_sub,map_sum]
    change powers e v n - _ = powers e v n - _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hp j,show powers e v n = polynomialMap e v (Polynomial.X^n) from rfl,
      polynomial_projection e v (p j) (Polynomial.X^n)]
    simp only [c,hp j]

theorem raw_real_polynomial (e : ι → ℝ) (v : ι → ℂ) (n : ℕ) :
    ∃ p : Polynomial ℝ, gramSchmidt ℂ (powers e v) n = polynomialMap e v p := by
  obtain ⟨p,_,_,hp⟩ := raw_monic_polynomial e v n
  exact ⟨p,hp⟩

/-- Normalization only multiplies a real polynomial by a real scalar.
At termination the representative may be the zero polynomial. -/
theorem normalized_real_polynomial_degree (e : ι → ℝ) (v : ι → ℂ) (n : ℕ) :
    ∃ p : Polynomial ℝ, p.degree ≤ (n : WithBot ℕ) ∧
      (gramSchmidtNormed ℂ (powers e v) n ≠ 0 → p.degree = (n : WithBot ℕ)) ∧
      gramSchmidtNormed ℂ (powers e v) n = polynomialMap e v p := by
  obtain ⟨p,hm,hd,hp⟩ := raw_monic_polynomial e v n
  let c : ℝ := ‖gramSchmidt ℂ (powers e v) n‖⁻¹
  refine ⟨c • p,(Polynomial.degree_smul_le c p).trans hd.le,?_,?_⟩
  · intro hn
    have hg : gramSchmidt ℂ (powers e v) n ≠ 0 := by
      intro hg
      exact hn (by simp [gramSchmidtNormed,hg])
    have hc : c ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hg)
    rw [Polynomial.degree_eq_natDegree (smul_ne_zero hc hm.ne_zero),
      Polynomial.natDegree_smul p hc,← Polynomial.degree_eq_natDegree hm.ne_zero,hd]
  · simp only [gramSchmidtNormed,map_smul,hp,c]
    exact congrArg (fun z : ℂ => z • polynomialMap e v p)
      (Complex.ofReal_inv ‖polynomialMap e v p‖).symm

theorem normalized_real_polynomial (e : ι → ℝ) (v : ι → ℂ) (n : ℕ) :
    ∃ p : Polynomial ℝ, gramSchmidtNormed ℂ (powers e v) n = polynomialMap e v p := by
  obtain ⟨p,_,_,hp⟩ := normalized_real_polynomial_degree e v n
  exact ⟨p,hp⟩

/-- The actual nonzero complex GS coordinates are orthonormal for their
real spectral weights, with no reality assumption on the seed. -/
theorem orthonormal_real_polynomials (e : ι → ℝ) (v : ι → ℂ) :
    ∃ p : ℕ → Polynomial ℝ,
      (∀ n, gramSchmidtNormed ℂ (powers e v) n = polynomialMap e v (p n)) ∧
      (∀ i j : FactorTwoFinite.GSIndex (powers e v),
        weightedDot e v (p i.val) (p j.val) = if i=j then 1 else 0) := by
  classical
  choose p hp using normalized_real_polynomial e v
  refine ⟨p,hp,?_⟩
  intro i j
  have hg := (orthonormal_iff_ite.mp (gramSchmidt_orthonormal' (powers e v))) i j
  rw [hp i.val,hp j.val,polynomial_inner] at hg
  by_cases hij : i=j <;> simpa [hij] using congrArg Complex.re hg

/-- Degree conventions are explicit: every representative has degree at most
its Krylov index, and every nonzero GS degree has exactly that polynomial degree. -/
theorem real_polynomials_with_degree (e : ι → ℝ) (v : ι → ℂ) :
    ∃ p : ℕ → Polynomial ℝ,
      (∀ n, (p n).degree ≤ (n : WithBot ℕ)) ∧
      (∀ n, gramSchmidtNormed ℂ (powers e v) n ≠ 0 → (p n).degree = (n : WithBot ℕ)) ∧
      (∀ n, gramSchmidtNormed ℂ (powers e v) n = polynomialMap e v (p n)) ∧
      (∀ i j : FactorTwoFinite.GSIndex (powers e v),
        weightedDot e v (p i.val) (p j.val) = if i=j then 1 else 0) := by
  classical
  choose p hd he hp using normalized_real_polynomial_degree e v
  refine ⟨p,hd,he,hp,?_⟩
  intro i j
  have hg := (orthonormal_iff_ite.mp (gramSchmidt_orthonormal' (powers e v))) i j
  rw [hp i.val,hp j.val,polynomial_inner] at hg
  by_cases hij : i=j <;> simpa [hij] using congrArg Complex.re hg

variable [DecidableEq ι]

/-- These are the literal powers in the generic physical state-chain API. -/
lemma powers_eq_stateSequence (e : ι → ℝ) (v : ι → ℂ) :
    powers e v = FactorTwoFinite.stateSequence (OperatorBridge.hamiltonian e) v := by
  funext n
  ext i
  simp [powers,polynomialMap,FactorTwoFinite.stateSequence,FactorTwo.hilbertSequence,
    FactorTwo.statePowerSequence,OperatorBridge.hamiltonian,Matrix.diagonal_pow,
    Matrix.mulVec_diagonal]

lemma diagonal_evolution (e : ι → ℝ) (v : ι → ℂ) (t : ℝ) (i : ι) :
    UnitaryEvolution.evolvedVector (OperatorBridge.hamiltonian e) v t i =
      OperatorBridge.phase (e i) t*v i := by
  have he := OperatorBridge.diagonalUnitary_eq_exp e t
  simp only [Complex.ofReal_neg,neg_mul] at he
  change (NormedSpace.exp ℂ ((-((t:ℂ)*Complex.I)) • OperatorBridge.hamiltonian e) *ᵥ v) i = _
  rw [← he]
  simp [OperatorBridge.diagonalUnitary,Matrix.mulVec_diagonal]

/-- The spectral amplitude is derived from the actual diagonal matrix
exponential and the seed's original complex coordinates. -/
theorem polynomial_amplitude (e : ι → ℝ) (v : ι → ℂ) (p : Polynomial ℝ) (t : ℝ) :
    ⟪polynomialMap e v p,
      UnitaryEvolution.evolvedVector (OperatorBridge.hamiltonian e) v t⟫_ℂ =
      ∑ i, ((‖v i‖^2*p.eval (e i) : ℝ) : ℂ)*OperatorBridge.phase (e i) t := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.inner_apply,polynomialMap_apply,diagonal_evolution,
    map_mul,RCLike.conj_ofReal,Complex.conj_ofReal]
  have h : v i * star (v i) = (‖v i‖^2 : ℝ) := by
    simpa [Complex.star_def,Complex.normSq_eq_norm_sq] using Complex.mul_conj' (v i)
  change OperatorBridge.phase (e i) t*v i*(((p.eval (e i) : ℝ) : ℂ)*star (v i)) = _
  calc
    _ = (((p.eval (e i) : ℝ) : ℂ)*OperatorBridge.phase (e i) t)*(v i*star (v i)) := by ring
    _ = _ := by rw [h]; push_cast; ring

/-- A real-polynomial spectral formula for every degree of the actual
complex-seed physical GS chain, including terminating zeros. -/
theorem physical_spectral_formula (e : ι → ℝ) (v : ι → ℂ) :
    ∃ p : ℕ → Polynomial ℝ, ∀ n t,
      ⟪gramSchmidtNormed ℂ (FactorTwoFinite.stateSequence (OperatorBridge.hamiltonian e) v) n,
        UnitaryEvolution.evolvedVector (OperatorBridge.hamiltonian e) v t⟫_ℂ =
        ∑ i, ((‖v i‖^2*(p n).eval (e i) : ℝ) : ℂ)*OperatorBridge.phase (e i) t := by
  choose p hp using normalized_real_polynomial e v
  refine ⟨p,?_⟩
  intro n t
  rw [← powers_eq_stateSequence, hp n]
  exact polynomial_amplitude e v (p n) t

/-- One and the same real polynomial family represents the physical chain,
is orthonormal on its nonzero degrees, and supplies the spectral amplitudes. -/
theorem physical_spectral_data (e : ι → ℝ) (v : ι → ℂ) :
    ∃ p : ℕ → Polynomial ℝ,
      (∀ n, (p n).degree ≤ (n : WithBot ℕ)) ∧
      (∀ n, gramSchmidtNormed ℂ
        (FactorTwoFinite.stateSequence (OperatorBridge.hamiltonian e) v) n ≠ 0 →
        (p n).degree = (n : WithBot ℕ)) ∧
      (∀ n, gramSchmidtNormed ℂ
        (FactorTwoFinite.stateSequence (OperatorBridge.hamiltonian e) v) n =
        polynomialMap e v (p n)) ∧
      (∀ i j : FactorTwoFinite.GSIndex
          (FactorTwoFinite.stateSequence (OperatorBridge.hamiltonian e) v),
        weightedDot e v (p i.val) (p j.val) = if i=j then 1 else 0) ∧
      (∀ n t, ⟪gramSchmidtNormed ℂ
        (FactorTwoFinite.stateSequence (OperatorBridge.hamiltonian e) v) n,
        UnitaryEvolution.evolvedVector (OperatorBridge.hamiltonian e) v t⟫_ℂ =
        ∑ i, ((‖v i‖^2*(p n).eval (e i) : ℝ) : ℂ)*OperatorBridge.phase (e i) t) := by
  obtain ⟨p,hd,he,hp,ho⟩ := real_polynomials_with_degree e v
  rw [powers_eq_stateSequence e v] at he hp ho
  refine ⟨p,hd,he,hp,ho,?_⟩
  intro n t
  rw [hp n]
  exact polynomial_amplitude e v (p n) t

/-- A normalized physical seed supplies a probability measure. -/
theorem weights_normalized (v : ι → ℂ) (hv : ‖UnitaryEvolution.hilbertVector v‖=1) :
    (∑ i, ‖v i‖^2)=1 := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) (UnitaryEvolution.hilbertVector v)
  rw [hv] at h
  simpa using h.symm

end Diagonal
end
end Krylov.PhysicalSpectralPolynomials
