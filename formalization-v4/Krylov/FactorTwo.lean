import Krylov.Bounds
import Krylov.Qubit

/-!
# Actual commutator and pure-state polynomial flags

This file proves the load-bearing Krylov/tensor total-degree flag inclusion
from the actual matrix commutator. It does not assume the inclusion as a
hypothesis. The final identification with an orthonormal state-Krylov product
probability projector is a separate step.
-/

namespace Krylov.FactorTwo
open Matrix
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Operator (ι : Type*) := Matrix ι ι ℂ

/-- The actual commutator as a complex-linear endomorphism. -/
def commutator (G : Operator ι) : Module.End ℂ (Operator ι) :=
  LinearMap.mulLeft ℂ G - LinearMap.mulRight ℂ G

@[simp] theorem commutator_apply (G A : Operator ι) :
    commutator G A = G * A - A * G := rfl

/-- Total-degree left/right polynomial flag. -/
def polynomialTensorFlag (G σ : Operator ι) (n : ℕ) : Submodule ℂ (Operator ι) :=
  Submodule.span ℂ {A | ∃ i j : ℕ, i + j ≤ n ∧ A = G ^ i * σ * G ^ j}

/-- Genuine Krylov flag of the actual matrix commutator and seed. -/
def operatorKrylovFlag (G σ : Operator ι) (n : ℕ) : Submodule ℂ (Operator ι) :=
  Submodule.span ℂ {A | ∃ k : ℕ, k ≤ n ∧ A = (commutator G ^ k) σ}

theorem tensor_monomial_mem (G σ : Operator ι) {i j n : ℕ} (hij : i + j ≤ n) :
    G ^ i * σ * G ^ j ∈ polynomialTensorFlag G σ n :=
  Submodule.subset_span ⟨i, j, hij, rfl⟩

theorem polynomialTensorFlag_mono (G σ : Operator ι) {m n : ℕ} (hmn : m ≤ n) :
    polynomialTensorFlag G σ m ≤ polynomialTensorFlag G σ n := by
  apply Submodule.span_mono
  rintro A ⟨i, j, hij, hA⟩
  exact ⟨i, j, le_trans hij hmn, hA⟩

/-- A direct Leibniz step, valid even without Hermiticity or a pure seed. -/
theorem commutator_monomial (G σ : Operator ι) (i j : ℕ) :
    commutator G (G ^ i * σ * G ^ j) =
      G ^ (i + 1) * σ * G ^ j - G ^ i * σ * G ^ (j + 1) := by
  rw [commutator_apply, pow_succ' G i, pow_succ G j]
  simp only [mul_assoc]

/-- The commutator raises total polynomial degree by at most one. -/
theorem commutator_flag_step (G σ : Operator ι) (n : ℕ) {A : Operator ι}
    (hA : A ∈ polynomialTensorFlag G σ n) :
    commutator G A ∈ polynomialTensorFlag G σ (n + 1) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨i, j, hij, rfl⟩ := hA
    rw [commutator_monomial]
    exact Submodule.sub_mem _ (tensor_monomial_mem G σ (by omega))
      (tensor_monomial_mem G σ (by omega))
  | zero => simp
  | add A B hA hB ihA ihB =>
    simpa only [map_add] using Submodule.add_mem _ ihA ihB
  | smul c A hA ihA =>
    simpa only [map_smul] using Submodule.smul_mem _ c ihA

/-- Every actual commutator power lies in the matching total-degree flag. -/
theorem commutator_power_mem (G σ : Operator ι) (k : ℕ) :
    (commutator G ^ k) σ ∈ polynomialTensorFlag G σ k := by
  induction k with
  | zero => simpa using tensor_monomial_mem G σ (i := 0) (j := 0) (n := 0) (by omega)
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact commutator_flag_step G σ k ih

/-- The load-bearing flag inclusion is derived from the commutator itself. -/
theorem operatorKrylovFlag_le_polynomialTensorFlag (G σ : Operator ι) (n : ℕ) :
    operatorKrylovFlag G σ n ≤ polynomialTensorFlag G σ n := by
  apply Submodule.span_le.mpr
  rintro A ⟨k, hkn, rfl⟩
  exact polynomialTensorFlag_mono G σ hkn (commutator_power_mem G σ k)

/-- Rank-one matrix with row-vectorization convention. -/
def outer (u v : ι → ℂ) : Operator ι := fun i j => u i * star (v j)

def pureSeed (ψ : ι → ℂ) : Operator ι := outer ψ ψ

theorem mul_outer (A : Operator ι) (u v : ι → ℂ) :
    A * outer u v = outer (A *ᵥ u) v := by
  ext i j
  simp [outer, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem outer_mul (u v : ι → ℂ) (A : Operator ι) :
    outer u v * A = outer u (Aᴴ *ᵥ v) := by
  ext i j
  simp only [outer, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    star_sum, StarMul.star_mul, star_star, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- For Hermitian `G`, each left/right monomial in the pure seed is the outer
product of the corresponding two genuine state-Krylov powers. -/
theorem pure_monomial (G : Operator ι) (hG : G.IsHermitian) (ψ : ι → ℂ) (i j : ℕ) :
    G ^ i * pureSeed ψ * G ^ j = outer ((G ^ i) *ᵥ ψ) ((G ^ j) *ᵥ ψ) := by
  unfold pureSeed
  rw [mul_outer, outer_mul, Matrix.conjTranspose_pow, hG.eq]

/-- Tensor total-degree flag expressed in the actual state-Krylov powers. -/
def pureTensorFlag (G : Operator ι) (ψ : ι → ℂ) (n : ℕ) : Submodule ℂ (Operator ι) :=
  Submodule.span ℂ {A | ∃ i j : ℕ, i + j ≤ n ∧
    A = outer ((G ^ i) *ᵥ ψ) ((G ^ j) *ᵥ ψ)}

theorem polynomialTensorFlag_eq_pureTensorFlag (G : Operator ι) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (n : ℕ) :
    polynomialTensorFlag G (pureSeed ψ) n = pureTensorFlag G ψ n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro A ⟨i, j, hij, rfl⟩
    rw [pure_monomial G hG]
    exact Submodule.subset_span ⟨i, j, hij, rfl⟩
  · apply Submodule.span_le.mpr
    rintro A ⟨i, j, hij, rfl⟩
    rw [← pure_monomial G hG]
    exact tensor_monomial_mem G (pureSeed ψ) hij

/-- The physical pure-state commutator Krylov flag is contained in the
state-power tensor flag. This includes stationary seeds, degenerate spectra,
and chains terminating before the nominal dimension. -/
theorem pure_operatorKrylovFlag_le (G : Operator ι) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (n : ℕ) :
    operatorKrylovFlag G (pureSeed ψ) n ≤ pureTensorFlag G ψ n := by
  rw [← polynomialTensorFlag_eq_pureTensorFlag G hG]
  exact operatorKrylovFlag_le_polynomialTensorFlag G (pureSeed ψ) n

@[simp] theorem outer_zero_left (v : ι → ℂ) : outer 0 v = 0 := by
  ext i j; simp [outer]
@[simp] theorem outer_zero_right (u : ι → ℂ) : outer u 0 = 0 := by
  ext i j; simp [outer]

theorem outer_add_left (u v w : ι → ℂ) : outer (u + v) w = outer u w + outer v w := by
  ext i j; simp [outer, add_mul]
theorem outer_add_right (u v w : ι → ℂ) : outer u (v + w) = outer u v + outer u w := by
  ext i j; simp [outer, mul_add]
theorem outer_smul_left (c : ℂ) (u v : ι → ℂ) : outer (c • u) v = c • outer u v := by
  ext i j; simp [outer, mul_assoc]
theorem outer_smul_right (c : ℂ) (u v : ι → ℂ) : outer u (c • v) = star c • outer u v := by
  ext i j; simp [outer, StarMul.star_mul, mul_left_comm, mul_comm, mul_assoc]

/-- Total-degree outer-product flag of an arbitrary vector sequence. -/
def sequenceTensorFlag (f : ℕ → ι → ℂ) (n : ℕ) : Submodule ℂ (Operator ι) :=
  Submodule.span ℂ {A | ∃ i j : ℕ, i + j ≤ n ∧ A = outer (f i) (f j)}

/-- Bilinear/antilinear span induction retains the total-degree cutoff. -/
theorem outer_mem_sequenceTensorFlag (f : ℕ → ι → ℂ) {i j n : ℕ}
    (hij : i + j ≤ n) {u v : ι → ℂ}
    (hu : u ∈ Submodule.span ℂ (f '' Set.Iic i))
    (hv : v ∈ Submodule.span ℂ (f '' Set.Iic j)) :
    outer u v ∈ sequenceTensorFlag f n := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨k, hki, rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, hlj, rfl⟩ := hv
      exact Submodule.subset_span ⟨k, l, by simpa using le_trans (Nat.add_le_add hki hlj) hij, rfl⟩
    | zero => simp
    | add v w hv hw ihv ihw =>
      rw [outer_add_right]
      exact Submodule.add_mem _ ihv ihw
    | smul c v hv ihv =>
      rw [outer_smul_right]
      exact Submodule.smul_mem _ _ ihv
  | zero => simp
  | add u w hu hw ihu ihw =>
    rw [outer_add_left]
    exact Submodule.add_mem _ ihu ihw
  | smul c u hu ihu =>
    rw [outer_smul_left]
    exact Submodule.smul_mem _ _ ihu

theorem sequenceTensorFlag_le_of_prefix_le (f g : ℕ → ι → ℂ)
    (hprefix : ∀ n : ℕ, Submodule.span ℂ (f '' Set.Iic n) ≤
      Submodule.span ℂ (g '' Set.Iic n)) (n : ℕ) :
    sequenceTensorFlag f n ≤ sequenceTensorFlag g n := by
  apply Submodule.span_le.mpr
  rintro A ⟨i, j, hij, rfl⟩
  apply outer_mem_sequenceTensorFlag g hij
  · exact hprefix i (Submodule.subset_span ⟨i, by simp, rfl⟩)
  · exact hprefix j (Submodule.subset_span ⟨j, by simp, rfl⟩)

theorem sequenceTensorFlag_eq_of_prefix_eq (f g : ℕ → ι → ℂ)
    (hprefix : ∀ n : ℕ, Submodule.span ℂ (f '' Set.Iic n) =
      Submodule.span ℂ (g '' Set.Iic n)) (n : ℕ) :
    sequenceTensorFlag f n = sequenceTensorFlag g n := by
  exact le_antisymm (sequenceTensorFlag_le_of_prefix_le f g (fun n => (hprefix n).le) n)
    (sequenceTensorFlag_le_of_prefix_le g f (fun n => (hprefix n).ge) n)

/-- The state sequence regarded in its actual finite-dimensional Hilbert space. -/
def hilbertSequence (f : ℕ → ι → ℂ) : ℕ → EuclideanSpace ℂ ι :=
  fun k => (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm (f k)

/-- Actual normalized Gram-Schmidt; zero vectors after termination are kept as
zeros, so no nondegeneracy or fixed positive chain-length assumption is needed. -/
def gramSchmidtSequence (f : ℕ → ι → ℂ) : ℕ → ι → ℂ :=
  fun k => WithLp.linearEquiv 2 ℂ (ι → ℂ) (gramSchmidtNormed ℂ (hilbertSequence f) k)

/-- The exact prefix-span identity for normalized Gram-Schmidt, transported
back to matrix-entry coordinates. -/
theorem gramSchmidtSequence_prefix (f : ℕ → ι → ℂ) (n : ℕ) :
    Submodule.span ℂ (gramSchmidtSequence f '' Set.Iic n) =
      Submodule.span ℂ (f '' Set.Iic n) := by
  have h := (span_gramSchmidtNormed (hilbertSequence f) (Set.Iic n)).trans
    (span_gramSchmidt_Iic ℂ (hilbertSequence f) n)
  have hm := congrArg (Submodule.map (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap) h
  simpa [Submodule.map_span, Set.image_image, Function.comp_def,
    gramSchmidtSequence, hilbertSequence] using hm

/-- The nonzero vectors really are orthonormal in the state Hilbert space. -/
theorem gramSchmidtSequence_orthonormal (f : ℕ → ι → ℂ) :
    Orthonormal ℂ (fun k : {k : ℕ | gramSchmidtNormed ℂ (hilbertSequence f) k ≠ 0} =>
      gramSchmidtNormed ℂ (hilbertSequence f) k) :=
  gramSchmidt_orthonormal' (hilbertSequence f)

/-- Gram-Schmidt preserves the total-degree product flag, not just each
one-factor span separately. -/
theorem sequenceTensorFlag_gramSchmidt (f : ℕ → ι → ℂ) (n : ℕ) :
    sequenceTensorFlag (gramSchmidtSequence f) n = sequenceTensorFlag f n :=
  sequenceTensorFlag_eq_of_prefix_eq _ _ (gramSchmidtSequence_prefix f) n

/-- Actual state-power sequence. -/
def statePowerSequence (G : Operator ι) (ψ : ι → ℂ) : ℕ → ι → ℂ :=
  fun k => (G ^ k) *ᵥ ψ

/-- The source's tensor flag expressed with the actual normalized
Gram-Schmidt state Krylov sequence. -/
def orthogonalTensorFlag (G : Operator ι) (ψ : ι → ℂ) (n : ℕ) :
    Submodule ℂ (Operator ι) :=
  sequenceTensorFlag (gramSchmidtSequence (statePowerSequence G ψ)) n

theorem orthogonalTensorFlag_eq_pureTensorFlag (G : Operator ι) (ψ : ι → ℂ) (n : ℕ) :
    orthogonalTensorFlag G ψ n = pureTensorFlag G ψ n := by
  exact sequenceTensorFlag_gramSchmidt (statePowerSequence G ψ) n

/-- The actual commutator Krylov flag is contained in the actual
orthonormalized state-Krylov total-degree product flag. -/
theorem pure_operatorKrylovFlag_le_orthogonalTensorFlag (G : Operator ι)
    (hG : G.IsHermitian) (ψ : ι → ℂ) (n : ℕ) :
    operatorKrylovFlag G (pureSeed ψ) n ≤ orthogonalTensorFlag G ψ n := by
  rw [orthogonalTensorFlag_eq_pureTensorFlag]
  exact pure_operatorKrylovFlag_le G hG ψ n

/-- Row vectorization into a genuine Euclidean (Hilbert--Schmidt) space. -/
def rowVectorize : Operator ι ≃ₗ[ℂ] EuclideanSpace ℂ (ι × ι) where
  toFun A := (WithLp.linearEquiv 2 ℂ ((ι × ι) → ℂ)).symm (fun p => A p.1 p.2)
  invFun v := fun i j => WithLp.linearEquiv 2 ℂ ((ι × ι) → ℂ) v (i, j)
  left_inv A := by ext i j; rfl
  right_inv v := by
    apply (WithLp.linearEquiv 2 ℂ ((ι × ι) → ℂ)).injective
    ext p; rcases p with ⟨i, j⟩; rfl
  map_add' A B := by
    apply (WithLp.linearEquiv 2 ℂ ((ι × ι) → ℂ)).injective
    ext p; rfl
  map_smul' c A := by
    apply (WithLp.linearEquiv 2 ℂ ((ι × ι) → ℂ)).injective
    ext p; rfl

/-- Row vectorization has exactly the Hilbert--Schmidt inner product. -/
theorem rowVectorize_inner (A B : Operator ι) :
    ⟪rowVectorize A, rowVectorize B⟫_ℂ = ∑ i, ∑ j, star (A i j) * B i j := by
  simp [rowVectorize, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type,
    mul_comm]

def vectorInner (u v : ι → ℂ) : ℂ := ∑ i, star (u i) * v i

theorem outer_inner (u v x y : ι → ℂ) :
    ⟪rowVectorize (outer u v), rowVectorize (outer x y)⟫_ℂ =
      vectorInner u x * star (vectorInner v y) := by
  rw [rowVectorize_inner]
  simp only [outer, vectorInner, star_sum, StarMul.star_mul, star_star,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def hilbertOuter (u v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (ι × ι) :=
  rowVectorize (outer (WithLp.linearEquiv 2 ℂ (ι → ℂ) u)
    (WithLp.linearEquiv 2 ℂ (ι → ℂ) v))

theorem hilbertOuter_inner (u v x y : EuclideanSpace ℂ ι) :
    ⟪hilbertOuter u v, hilbertOuter x y⟫_ℂ = ⟪u, x⟫_ℂ * star ⟪v, y⟫_ℂ := by
  rw [hilbertOuter, hilbertOuter, outer_inner]
  simp [vectorInner, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Tensoring an orthonormal state family with its conjugate produces an
orthonormal family in the actual Hilbert--Schmidt space. -/
theorem hilbertOuter_orthonormal {κ : Type*} (f : κ → EuclideanSpace ℂ ι)
    (hf : Orthonormal ℂ f) :
    Orthonormal ℂ (fun p : κ × κ => hilbertOuter (f p.1) (f p.2)) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro p q
  rw [hilbertOuter_inner, orthonormal_iff_ite.mp hf, orthonormal_iff_ite.mp hf]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [h1, h2, Prod.ext_iff]

/-- The actual rank-one amplitude factorization gives the product of state
probabilities appearing in the factor-two theorem. -/
theorem hilbertOuter_probability (u v x : EuclideanSpace ℂ ι) :
    ‖⟪hilbertOuter u v, hilbertOuter x x⟫_ℂ‖ ^ 2 =
      ‖⟪u, x⟫_ℂ‖ ^ 2 * ‖⟪v, x⟫_ℂ‖ ^ 2 := by
  rw [hilbertOuter_inner, norm_mul, norm_star, mul_pow]

/-- Physical flags transported into the Hilbert--Schmidt
coordinate space, so their orthogonal projections are genuine Hilbert-space
orthogonal projections rather than formal symbols. -/
def hilbertOperatorFlag (G : Operator ι) (ψ : ι → ℂ) (n : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (ι × ι)) :=
  (operatorKrylovFlag G (pureSeed ψ) n).map rowVectorize.toLinearMap

def hilbertTensorFlag (G : Operator ι) (ψ : ι → ℂ) (n : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (ι × ι)) :=
  (orthogonalTensorFlag G ψ n).map rowVectorize.toLinearMap

theorem hilbert_flag_inclusion (G : Operator ι) (hG : G.IsHermitian)
    (ψ : ι → ℂ) (n : ℕ) : hilbertOperatorFlag G ψ n ≤ hilbertTensorFlag G ψ n :=
  Submodule.map_mono (pure_operatorKrylovFlag_le_orthogonalTensorFlag G hG ψ n)

/-- Actual physical Krylov flags supply the source's geometric tail inequality. -/
theorem physical_projection_tail (G : Operator ι) (hG : G.IsHermitian)
    (ψ x : ι → ℂ) (n : ℕ) :
    1 - ‖(hilbertTensorFlag G ψ n).orthogonalProjection (rowVectorize (pureSeed x))‖ ^ 2 ≤
      1 - ‖(hilbertOperatorFlag G ψ n).orthogonalProjection (rowVectorize (pureSeed x))‖ ^ 2 := by
  exact Krylov.nested_projection_tail_le _ _ (hilbert_flag_inclusion G hG ψ n) _ 1

section FiniteOrthonormalProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {κ : Type*} [DecidableEq κ]

/-- Finite orthonormal-coordinate span. -/
def finiteOrthoSpan (v : κ → E) (s : Finset κ) : Submodule ℂ E :=
  Submodule.span ℂ (v '' (s : Set κ))

/-- The actual orthogonal projection onto a finite orthonormal span is its
coordinate sum. -/
theorem orthonormal_projection_eq_sum (v : κ → E) (hv : Orthonormal ℂ v)
    (s : Finset κ) (x : E) :
    ((finiteOrthoSpan v s).orthogonalProjection x : E) =
      ∑ i ∈ s, ⟪v i, x⟫_ℂ • v i := by
  apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, hi, rfl⟩ := hw
      rw [inner_sub_left, hv.inner_left_sum _ hi, inner_conj_symm]
      simp
    | zero => simp
    | add u w hu hw ihu ihw => simp only [inner_add_right, ihu, ihw, add_zero]
    | smul c w hw ihw => simp only [inner_smul_right, ihw, mul_zero]

/-- Projection mass is exactly the sum of squared coordinate amplitudes. -/
theorem orthonormal_projection_mass (v : κ → E) (hv : Orthonormal ℂ v)
    (s : Finset κ) (x : E) :
    ‖(finiteOrthoSpan v s).orthogonalProjection x‖ ^ 2 =
      ∑ i ∈ s, ‖⟪v i, x⟫_ℂ‖ ^ 2 := by
  change ‖((finiteOrthoSpan v s).orthogonalProjection x : E)‖ ^ 2 = _
  rw [orthonormal_projection_eq_sum v hv s x, @norm_sq_eq_re_inner ℂ]
  rw [hv.inner_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (star ⟪v i, x⟫_ℂ * ⟪v i, x⟫_ℂ).re = _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

end FiniteOrthonormalProjection

/-- Actual tensor projection mass is the product-probability sum for any
finite subset of the orthonormal state-family product coordinates. -/
theorem tensor_projection_mass {κ : Type*} [DecidableEq κ]
    (f : κ → EuclideanSpace ℂ ι) (hf : Orthonormal ℂ f)
    (s : Finset (κ × κ)) (x : EuclideanSpace ℂ ι) :
    ‖(finiteOrthoSpan (fun p : κ × κ => hilbertOuter (f p.1) (f p.2)) s).orthogonalProjection (hilbertOuter x x)‖ ^ 2 =
      ∑ p ∈ s, ‖⟪f p.1, x⟫_ℂ‖ ^ 2 * ‖⟪f p.2, x⟫_ℂ‖ ^ 2 := by
  rw [orthonormal_projection_mass _ (hilbertOuter_orthonormal f hf)]
  apply Finset.sum_congr rfl
  intro p _
  exact hilbertOuter_probability _ _ _

end
end Krylov.FactorTwo
