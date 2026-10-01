import Krylov.QubitSourceAPI

/-! The three-site Jacobi realization uses the actual normalized GS process,
including either terminating endpoint and arbitrary signed or zero frequency. -/
namespace Krylov.ThreeAtomSourceAPI
open Matrix Qubit FactorTwoFinite PerturbedDynamics
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000

abbrev Space := EuclideanSpace ℂ (Fin 3)
def e (i : Fin 3) : Space := UnitaryEvolution.hilbertVector (basisVector i)
def L (a b : ℂ) : Space →L[ℂ] Space := PureShortTime.stateGenerator (jacobi a b)
def v (a b : ℂ) : Fin 3 → Space := ![e 0,a • e 1,(a*b) • e 2]

lemma e_inner (i : Fin 3) (x : Space) : ⟪e i,x⟫_ℂ=x i := by
  simp [e,UnitaryEvolution.hilbertVector,PiLp.inner_apply,RCLike.inner_apply,
    basisVector,Matrix.one_apply]

lemma e_norm (i : Fin 3) : ‖e i‖=1 := by
  have h : ‖e i‖^2=1 := by rw [@norm_sq_eq_re_inner ℂ,e_inner]; simp [e,UnitaryEvolution.hilbertVector,basisVector,Matrix.one_apply]
  nlinarith [norm_nonneg (e i)]

lemma L_e_zero (a b : ℂ) : L a b (e 0)=a • e 1 := by
  rw [L,e,PureShortTime.stateGenerator_apply,jacobi_lanczos_zero]
  rfl
lemma L_e_one (a b : ℂ) : L a b (e 1)=a • e 0+b • e 2 := by
  rw [L,e,PureShortTime.stateGenerator_apply,jacobi_lanczos_one]
  rfl
lemma L_e_two (a b : ℂ) : L a b (e 2)=b • e 1 := by
  rw [L,e,PureShortTime.stateGenerator_apply,jacobi_lanczos_two]
  rfl

lemma v_recurrences (a b : ℂ) :
    L a b (v a b 0)=v a b 1 ∧
    L a b (v a b 1)=v a b 2+a^2 • v a b 0 ∧
    L a b (v a b 2)=b^2 • v a b 1 := by
  constructor
  · exact L_e_zero a b
  constructor
  · change L a b (a • e 1)=(a*b) • e 2+a^2 • e 0
    rw [map_smul,L_e_one,smul_add,smul_smul,smul_smul]
    simp [pow_two,add_comm]
  · change L a b ((a*b) • e 2)=b^2 • (a • e 1)
    rw [map_smul,L_e_two,smul_smul,smul_smul]
    congr 1; ring

lemma v_orthogonal (a b : ℂ) : Pairwise (fun i j => ⟪v a b i,v a b j⟫_ℂ=0) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [v,PiLp.inner_apply,RCLike.inner_apply,e,UnitaryEvolution.hilbertVector,
      basisVector,Matrix.one_apply,Fin.sum_univ_succ]

lemma power_one (a b : ℂ) : powerSequence (L a b) (e 0) 1 = v a b 1 := by
  simpa [powerSequence,v] using L_e_zero a b
lemma power_two (a b : ℂ) : powerSequence (L a b) (e 0) 2 = v a b 2+a^2 • v a b 0 := by
  change L a b (L a b (e 0)) = _
  rw [L_e_zero]
  exact (v_recurrences a b).2.1

lemma v_triangular (a b : ℂ) (i : Fin 3) :
    v a b i-(1:ℂ) • powerSequence (L a b) (e 0) i.val ∈
      CertifiedGS.previousSpan (powerSequence (L a b) (e 0)) i.val := by
  fin_cases i
  · simp [v,powerSequence]
  · simp [power_one]
  · change v a b 2-(1:ℂ) • powerSequence (L a b) (e 0) 2 ∈ _
    rw [one_smul,power_two,sub_add_eq_sub_sub,sub_self,zero_sub]
    apply Submodule.neg_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨0,by norm_num,by simp [powerSequence,v]⟩

lemma powers_mem (a b : ℂ) (k : ℕ) :
    powerSequence (L a b) (e 0) k ∈ Submodule.span ℂ (Set.range (v a b)) := by
  have hv (i : Fin 3) : v a b i ∈ Submodule.span ℂ (Set.range (v a b)) :=
    Submodule.subset_span ⟨i,rfl⟩
  have hi : ∀ x ∈ Submodule.span ℂ (Set.range (v a b)),
      L a b x ∈ Submodule.span ℂ (Set.range (v a b)) := by
    apply ConcreteChains.span_range_invariant (L a b).toLinearMap
    intro i
    fin_cases i
    · change L a b (v a b 0) ∈ _
      rw [(v_recurrences a b).1]; exact hv 1
    · change L a b (v a b 1) ∈ _
      rw [(v_recurrences a b).2.1]
      exact Submodule.add_mem _ (hv 2) (Submodule.smul_mem _ _ (hv 0))
    · change L a b (v a b 2) ∈ _
      rw [(v_recurrences a b).2.2]
      exact Submodule.smul_mem _ _ (hv 1)
  induction k with
  | zero => simpa [powerSequence,v] using hv 0
  | succ k ih => simpa [powerSequence,pow_succ',ContinuousLinearMap.mul_apply] using hi _ ih

/-- Complete padded GS formula for any two complex Jacobi couplings. -/
theorem generic_jacobi_complexity (a b : ℂ) (x : Space) :
    complexity (powerSequence (L a b) (e 0)) x =
      ∑ i : Fin 3, (i.val:ℝ)*(‖⟪v a b i,x⟫_ℂ‖^2/‖v a b i‖^2) :=
  CertifiedGS.complexity_eq_of_triangular _ _ (fun _ => 1) (fun _ => one_ne_zero)
    (v_triangular a b) (v_orthogonal a b) (powers_mem a b) x

lemma scaled_e_probability (c : ℂ) (hc : c ≠ 0) (i : Fin 3) (x : Space) :
    ‖⟪c • e i,x⟫_ℂ‖^2/‖c • e i‖^2 = ‖x i‖^2 := by
  simp only [inner_smul_left,e_inner,norm_mul,norm_star,Complex.norm_conj,norm_smul,e_norm,mul_one,mul_pow]
  exact mul_div_cancel_left₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))


def generator (μ ω : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := (ω:ℂ) • threeAtomJacobi μ

lemma generator_jacobi (μ ω : ℝ) :
    generator μ ω = jacobi ((ω:ℂ)*(Real.sqrt μ:ℂ)) ((ω:ℂ)*(Real.sqrt (1-μ):ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [generator,threeAtomJacobi,jacobi]

lemma evolved_coordinates {μ : ℝ} (hμ : μ ∈ Set.Icc (0:ℝ) 1) (ω t : ℝ) (i : Fin 3) :
    UnitaryEvolution.evolvedVector (generator μ ω) (basisVector 0) t i = amplitudes μ (ω*t) i := by
  have he := congrFun (threeAtom_exp_amplitudes hμ (ω*t)) i
  have hc : (-((t:ℂ)*Complex.I)) • generator μ ω =
      (-(((ω*t:ℝ):ℂ)*Complex.I)) • threeAtomJacobi μ := by
    rw [generator,smul_smul]
    congr 1
    push_cast
    ring
  simpa [UnitaryEvolution.evolvedVector,UnitaryEvolution.propagator,UnitaryEvolution.hilbertVector,basisVector,
    Matrix.mulVec, dotProduct,Matrix.one_apply,hc] using he

lemma evolved_one_zero {μ : ℝ} (hμ : μ ∈ Set.Icc (0:ℝ) 1) (ω t : ℝ)
    (ha : (ω:ℂ)*(Real.sqrt μ:ℂ)=0) :
    UnitaryEvolution.evolvedVector (generator μ ω) (basisVector 0) t 1=0 := by
  rcases mul_eq_zero.mp ha with hw | hs
  · have hω : ω=0 := Complex.ofReal_eq_zero.mp hw
    simp [evolved_coordinates hμ,amplitudes,hω]
  · have hs' : Real.sqrt μ=0 := Complex.ofReal_eq_zero.mp hs
    simp [evolved_coordinates hμ,amplitudes,hs']

lemma evolved_two_zero {μ : ℝ} (hμ : μ ∈ Set.Icc (0:ℝ) 1) (ω t : ℝ)
    (hab : ((ω:ℂ)*(Real.sqrt μ:ℂ))*((ω:ℂ)*(Real.sqrt (1-μ):ℂ))=0) :
    UnitaryEvolution.evolvedVector (generator μ ω) (basisVector 0) t 2=0 := by
  rw [evolved_coordinates hμ,amplitudes]
  change ((Real.sqrt (μ*(1-μ))*(Real.cos (ω*t)-1):ℝ):ℂ)=0
  rw [Real.sqrt_mul hμ.1]
  rcases mul_eq_zero.mp hab with ha | hb
  · rcases mul_eq_zero.mp ha with hw | hs
    · have hω : ω=0 := Complex.ofReal_eq_zero.mp hw
      simp [hω]
    · have hs' : Real.sqrt μ=0 := Complex.ofReal_eq_zero.mp hs
      simp [hs']
  · rcases mul_eq_zero.mp hb with hw | hs
    · have hω : ω=0 := Complex.ofReal_eq_zero.mp hw
      simp [hω]
    · have hs' : Real.sqrt (1-μ)=0 := Complex.ofReal_eq_zero.mp hs
      simp [hs']

/-- Literal generic state GS complexity of the Jacobi realization, including
μ=0, μ=1 and any signed or zero spectral gap. -/
theorem state_complexity_eq {μ : ℝ} (hμ : μ ∈ Set.Icc (0:ℝ) 1) (ω t : ℝ) :
    complexity (stateSequence (generator μ ω) (basisVector 0))
      (UnitaryEvolution.evolvedVector (generator μ ω) (basisVector 0) t) =
        threeAtom μ (ω*t) := by
  let a : ℂ := (ω:ℂ)*(Real.sqrt μ:ℂ)
  let b : ℂ := (ω:ℂ)*(Real.sqrt (1-μ):ℂ)
  let x := UnitaryEvolution.evolvedVector (generator μ ω) (basisVector 0) t
  have hf : powerSequence (L a b) (e 0)=stateSequence (generator μ ω) (basisVector 0) := by
    funext k
    change powerSequence (L a b) (e 0) k =
      UnitaryEvolution.hilbertVector ((generator μ ω)^k *ᵥ basisVector 0)
    rw [← PureShortTime.state_power,generator_jacobi]
    rfl
  have hg := generic_jacobi_complexity a b x
  rw [hf] at hg
  rw [hg]
  have hp1 : ‖⟪v a b 1,x⟫_ℂ‖^2/‖v a b 1‖^2=‖x 1‖^2 := by
    by_cases ha : a=0
    · have hx := evolved_one_zero hμ ω t ha
      simp [v,ha,x,hx]
    · exact scaled_e_probability a ha 1 x
  have hp2 : ‖⟪v a b 2,x⟫_ℂ‖^2/‖v a b 2‖^2=‖x 2‖^2 := by
    by_cases hab : a*b=0
    · have hx := evolved_two_zero hμ ω t hab
      change ‖⟪(a*b) • e 2,x⟫_ℂ‖^2/‖(a*b) • e 2‖^2=‖x 2‖^2
      simp [hab,x,hx]
    · exact scaled_e_probability (a*b) hab 2 x
  have hcoord (i : Fin 3) : x i =
      NormedSpace.exp ℂ ((-(((ω*t:ℝ):ℂ)*Complex.I)) • threeAtomJacobi μ) i 0 := by
    dsimp only [x]
    rw [evolved_coordinates hμ]
    exact (congrFun (threeAtom_exp_amplitudes hμ (ω*t)) i).symm
  have heq : (∑ i : Fin 3, (i.val:ℝ)*(‖⟪v a b i,x⟫_ℂ‖^2/‖v a b i‖^2)) =
      matrixChainComplexity μ (ω*t) := by
    unfold matrixChainComplexity
    apply Finset.sum_congr rfl
    intro i _
    fin_cases i
    · simp
    · simpa using hp1.trans (congrArg (fun z : ℂ => ‖z‖^2) (hcoord 1))
    · simpa using congrArg (fun r : ℝ => 2*r)
        (hp2.trans (congrArg (fun z : ℂ => ‖z‖^2) (hcoord 2)))
  rw [heq,matrixChainComplexity_eq hμ]

/-- The same conclusion in the continuous-linear-operator actualComplexity API. -/
theorem actual_complexity_eq {μ : ℝ} (hμ : μ ∈ Set.Icc (0:ℝ) 1) (ω t : ℝ) :
    actualComplexity (PureShortTime.stateGenerator (generator μ ω)) (e 0) t =
      threeAtom μ (ω*t) := by
  change actualComplexity _ (UnitaryEvolution.hilbertVector (basisVector 0)) t = _
  rw [PureShortTime.stateComplexity_physical]
  exact state_complexity_eq hμ ω t

end
end Krylov.ThreeAtomSourceAPI
