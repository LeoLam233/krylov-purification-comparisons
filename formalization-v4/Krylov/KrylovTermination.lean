import Krylov.FactorTwoFinite

/-! Gram-Schmidt on a genuine power sequence has no internal zero gaps.
Thus the retained natural degrees really are consecutive Krylov indices,
and every active degree is strictly below the ambient dimension. -/
namespace Krylov.KrylovTermination
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma normed_zero_iff (f : ℕ → E) (n : ℕ) :
    gramSchmidtNormed ℂ f n=0 ↔ gramSchmidt ℂ f n=0 := by
  simp [gramSchmidtNormed,smul_eq_zero]

lemma gram_zero_iff_mem (f : ℕ → E) (n : ℕ) :
    gramSchmidt ℂ f n=0 ↔ f n ∈ Submodule.span ℂ (f '' Set.Iio n) := by
  let S := Submodule.span ℂ (f '' Set.Iio n)
  have hprev : ∀ i<n, gramSchmidt ℂ f i ∈ S := by
    intro i hi
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iio.mpr hi))
      (gramSchmidt_mem_span ℂ f le_rfl)
  have hi : ∀ x∈S, ⟪gramSchmidt ℂ f n,x⟫_ℂ=0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i,hin,rfl⟩ := hx
      exact gramSchmidt_inv_triangular ℂ f hin
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_right,ihx,ihy]
    | smul c x hx ih => simp [inner_smul_right,ih]
  constructor
  · intro hz
    rw [gramSchmidt_def'' ℂ f n,hz,zero_add]
    apply S.sum_mem
    intro i hin
    apply S.smul_mem
    exact hprev i (by simpa using hin)
  · intro hf
    have hgs : gramSchmidt ℂ f n ∈ S := by
      have he := gramSchmidt_def'' ℂ f n
      have hsum : (∑ i ∈ Finset.Iio n,
          (⟪gramSchmidt ℂ f i,f n⟫_ℂ/(‖gramSchmidt ℂ f i‖:ℂ)^2) • gramSchmidt ℂ f i) ∈ S := by
        apply S.sum_mem
        intro i hin
        exact S.smul_mem _ (hprev i (by simpa using hin))
      have hsub := S.sub_mem hf hsum
      have heq : f n - (∑ i ∈ Finset.Iio n,
          (⟪gramSchmidt ℂ f i,f n⟫_ℂ/(‖gramSchmidt ℂ f i‖:ℂ)^2) • gramSchmidt ℂ f i) = gramSchmidt ℂ f n := by
        exact sub_eq_iff_eq_add.mpr he
      simpa only [heq] using hsub
    exact inner_self_eq_zero.mp (hi _ hgs)

def sequence (L : E →L[ℂ] E) (v : E) (n : ℕ) : E := (L^n) v

def previousSpan (L : E →L[ℂ] E) (v : E) (n : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ (sequence L v '' Set.Iio n)

@[simp] lemma sequence_succ (L : E →L[ℂ] E) (v : E) (n : ℕ) :
    sequence L v (n+1)=L (sequence L v n) := by
  simp [sequence,pow_succ',ContinuousLinearMap.mul_apply]

lemma previousSpan_invariant (L : E →L[ℂ] E) (v : E) (n : ℕ)
    (hn : sequence L v n ∈ previousSpan L v n) :
    ∀ x∈previousSpan L v n,L x∈previousSpan L v n := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    have hi' : i<n := hi
    rw [← sequence_succ]
    by_cases h : i+1<n
    · exact Submodule.subset_span ⟨i+1,h,rfl⟩
    · have he : i+1=n := by omega
      simpa [he] using hn
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma later_mem_previous (L : E →L[ℂ] E) (v : E) (n : ℕ)
    (hn : sequence L v n ∈ previousSpan L v n) :
    ∀ k,n≤k → sequence L v k∈previousSpan L v n := by
  intro k hk
  induction k,hk using Nat.le_induction with
  | base => exact hn
  | succ k hk ih => rw [sequence_succ]; exact previousSpan_invariant L v n hn _ ih

theorem zero_forces_later_zero (L : E →L[ℂ] E) (v : E) {n k : ℕ}
    (hn : gramSchmidtNormed ℂ (sequence L v) n=0) (hnk : n≤k) :
    gramSchmidtNormed ℂ (sequence L v) k=0 := by
  apply (normed_zero_iff _ _).2
  apply (gram_zero_iff_mem _ _).2
  have hmem := (gram_zero_iff_mem _ n).1 ((normed_zero_iff _ _).1 hn)
  have h := later_mem_previous L v n hmem k hnk
  exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hnk)) h

theorem nonzero_downward (L : E →L[ℂ] E) (v : E) {n k : ℕ}
    (hk : gramSchmidtNormed ℂ (sequence L v) k ≠0) (hnk : n≤k) :
    gramSchmidtNormed ℂ (sequence L v) n ≠0 := by
  intro hn
  exact hk (zero_forces_later_zero L v hn hnk)

theorem active_index_lt_finrank [FiniteDimensional ℂ E]
    (L : E →L[ℂ] E) (v : E) (k : FactorTwoFinite.GSIndex (sequence L v)) :
    k.val < Module.finrank ℂ E := by
  let e : Fin (k.val+1) → FactorTwoFinite.GSIndex (sequence L v) :=
    fun i => ⟨i.val, nonzero_downward L v k.property (by omega)⟩
  have he : Function.Injective e := by
    intro i j h
    exact Fin.ext (congrArg Subtype.val h)
  have hli := (FactorTwoFinite.gsFamily_orthonormal (sequence L v)).linearIndependent.comp e he
  have hb := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hb
  omega

end
end Krylov.KrylovTermination
