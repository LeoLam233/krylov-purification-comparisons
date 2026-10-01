import Krylov.ConcreteChains

namespace Krylov.FiniteSpectralSupport
open Matrix ConcreteChains
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagonalEnd (e : ι → ℂ) : Module.End ℂ (ι → ℂ) where
  toFun x i := e i*x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp; ring

def atoms (e v : ι → ℂ) : Finset ℂ := by
  classical
  exact (Finset.univ.filter fun i => v i ≠ 0).image e

def slice (e v : ι → ℂ) (a : ℂ) : ι → ℂ := fun i => if e i=a then v i else 0

lemma active_mem (e v : ι → ℂ) {i : ι} (hi : v i ≠ 0) : e i ∈ atoms e v := by
  classical
  exact Finset.mem_image.mpr ⟨i,by simp [hi],rfl⟩


def atomWeight (e v : ι → ℂ) (a : ℂ) : ℝ :=
  ∑ i, if e i=a then ‖v i‖^2 else 0

/-- The support criterion is exactly strictly positive merged spectral weight. -/
theorem mem_atoms_iff_weight_pos (e v : ι → ℂ) (a : ℂ) :
    a ∈ atoms e v ↔ 0 < atomWeight e v a := by
  classical
  constructor
  · intro ha
    obtain ⟨i,hi,hia⟩ := Finset.mem_image.mp ha
    have hvi : v i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hp : 0 < (if e i=a then ‖v i‖^2 else 0 : ℝ) := by
      simp [hia, sq_pos_of_pos (norm_pos_iff.mpr hvi)]
    exact lt_of_lt_of_le hp (Finset.single_le_sum (f := fun j => if e j=a then ‖v j‖^2 else (0:ℝ)) (fun j _ => by positivity) (Finset.mem_univ i))
  · intro hp
    by_contra ha
    have hz : atomWeight e v a = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hia : e i=a
      · have hv : v i=0 := by
          by_contra hv
          exact ha (hia ▸ active_mem e v hv)
        simp [hv]
      · simp [hia]
    rw [hz] at hp
    exact (lt_irrefl 0) hp

lemma slice_ne_zero (e v : ι → ℂ) (a : ↑(atoms e v)) : slice e v a ≠ 0 := by
  classical
  obtain ⟨i,hi,hia⟩ := Finset.mem_image.mp a.property
  have hvi : v i ≠ 0 := (Finset.mem_filter.mp hi).2
  intro hzero
  have h := congrFun hzero i
  simp [slice,hia] at h
  exact hvi h

lemma slice_eigenvector (e v : ι → ℂ) (a : ↑(atoms e v)) :
    (diagonalEnd e).HasEigenvector a (slice e v a) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_,slice_ne_zero e v a⟩
  ext i
  by_cases h : e i = a
  · simp [diagonalEnd,slice,h]
  · simp [diagonalEnd,slice,h]

lemma slices_independent (e v : ι → ℂ) :
    LinearIndependent ℂ (fun a : ↑(atoms e v) => slice e v a) :=
  Module.End.eigenvectors_linearIndependent' (diagonalEnd e) _ Subtype.coe_injective _
    (slice_eigenvector e v)

lemma power_apply (e v : ι → ℂ) (n : ℕ) (i : ι) :
    ((diagonalEnd e)^n) v i = (e i)^n*v i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',Module.End.mul_apply]
    change e i*(((diagonalEnd e)^n) v i) = _
    rw [ih,pow_succ']; ring

lemma polynomial_apply (e v : ι → ℂ) (p : Polynomial ℂ) (i : ι) :
    (Polynomial.aeval (diagonalEnd e) p) v i = p.eval (e i)*v i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add,hp,hq,add_mul]
  | monomial k a =>
    simp [Polynomial.aeval_monomial,Module.End.mul_apply,power_apply,
      Polynomial.eval_monomial,mul_assoc]

lemma slice_mem_cyclic (e v : ι → ℂ) (a : ↑(atoms e v)) :
    slice e v a ∈ cyclicSpan (diagonalEnd e) v := by
  classical
  let p := Lagrange.interpolate (atoms e v) (fun z : ℂ => z) (fun z => if z=a then 1 else 0)
  have he : slice e v a = (Polynomial.aeval (diagonalEnd e) p) v := by
    ext i
    rw [polynomial_apply]
    by_cases hi : v i=0
    · simp [slice,hi]
    · have hp : p.eval (e i) = if e i=a then 1 else 0 :=
        Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => h) (active_mem e v hi)
      rw [hp]
      by_cases h : e i=a <;> simp [slice,h]
  rw [he]
  exact polynomial_mem_cyclicSpan _ _ _

lemma seed_eq_sum_slices (e v : ι → ℂ) :
    v = ∑ a : ↑(atoms e v), slice e v a := by
  classical
  ext i
  simp only [Finset.sum_apply,slice]
  by_cases hi : v i=0
  · simp [hi]
  · let a : ↑(atoms e v) := ⟨e i,active_mem e v hi⟩
    rw [Finset.sum_eq_single a]
    · simp [a]
    · intro b _ hb
      have hn : e i ≠ (b : ℂ) := by
        intro he
        apply hb
        exact Subtype.ext he.symm
      simp [hn]
    · simp

/-- Repeated spectral values are merged and zero-weight values removed.
The resulting number of atoms is exactly the true cyclic dimension. -/
theorem cyclic_dimension (e v : ι → ℂ) :
    Module.finrank ℂ (cyclicSpan (diagonalEnd e) v) = (atoms e v).card := by
  classical
  have hspan : cyclicSpan (diagonalEnd e) v =
      Submodule.span ℂ (Set.range (fun a : ↑(atoms e v) => slice e v a)) := by
    apply le_antisymm
    · apply cyclicSpan_le_of_invariant
      · have hsum : (∑ a : ↑(atoms e v), slice e v a) ∈
            Submodule.span ℂ (Set.range (fun a : ↑(atoms e v) => slice e v a)) :=
          Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a,rfl⟩
        simpa only [← seed_eq_sum_slices e v] using hsum
      · apply span_range_invariant
        intro a
        rw [(slice_eigenvector e v a).apply_eq_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a,rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact slice_mem_cyclic e v a
  rw [hspan,finrank_span_eq_card (slices_independent e v)]
  simp
end
end Krylov.FiniteSpectralSupport
