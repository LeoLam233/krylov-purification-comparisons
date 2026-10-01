import Krylov.PhysicalSpectralPolynomials
import Krylov.HermitianSpectralSupport
import Krylov.ActualReturnBounds
import Krylov.PureShortTime

namespace Krylov.HermitianSpectralFormula
open Matrix UniversalQubit UnitaryCovariance UnitaryEvolution
open FactorTwoFinite PhysicalSpectralPolynomials
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 3000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma repr_hilbertVector {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (ψ : ι → ℂ) :
    hH.eigenvectorBasis.repr (hilbertVector ψ) = hilbertVector ((energyBasis hH)ᴴ *ᵥ ψ) := by
  ext i
  simp [OrthonormalBasis.repr_apply_apply,PiLp.inner_apply,RCLike.inner_apply,
    hilbertVector,Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,energyBasis,mul_comm]

lemma mulVecLin_power (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (n : ℕ) :
    (H.mulVecLin^n) ψ=H^n *ᵥ ψ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [pow_succ',Module.End.mul_apply,Matrix.mulVecLin_apply,ih,Matrix.mulVec_mulVec]

lemma cyclic_hilbert_coordinates (H : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    (FactorTwoFinite.cyclicSpan (stateSequence H ψ)).map
      (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap =
        ConcreteChains.cyclicSpan H.mulVecLin ψ := by
  unfold FactorTwoFinite.cyclicSpan ConcreteChains.cyclicSpan
  rw [Submodule.map_span,← Set.range_comp]
  apply congrArg (fun f : ℕ → (ι → ℂ) => Submodule.span ℂ (Set.range f))
  funext n
  simp [Function.comp_def,stateSequence,FactorTwo.hilbertSequence,FactorTwo.statePowerSequence,
    mulVecLin_power]

/-- Exact chain length in the actual normalized-Gram–Schmidt API equals the
number of merged spectral atoms having strictly positive weight. -/
theorem gs_length_positive_atoms {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (ψ : ι → ℂ) :
    Fintype.card (GSIndex (stateSequence H ψ)) =
      (FiniteSpectralSupport.atoms (fun i => (hH.eigenvalues i : ℂ))
        ((energyBasis hH)ᴴ *ᵥ ψ)).card := by
  have hseq : PerturbedDynamics.powerSequence (PureShortTime.stateGenerator H) (hilbertVector ψ) =
      stateSequence H ψ := by
    funext n
    exact PureShortTime.state_power H ψ n
  have hd := ActualReturnBounds.length_eq_cyclic_finrank
    (PureShortTime.stateGenerator H) (hilbertVector ψ)
  unfold ActualReturnBounds.chainLength at hd
  rw [hseq] at hd
  rw [hd,← (WithLp.linearEquiv 2 ℂ (ι → ℂ)).finrank_map_eq,
    cyclic_hilbert_coordinates]
  exact HermitianSpectralSupport.cyclic_dimension hH ψ

lemma state_coordinates {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (ψ : ι → ℂ) (n : ℕ) :
    hH.eigenvectorBasis.repr (stateSequence H ψ n) =
      stateSequence (OperatorBridge.hamiltonian hH.eigenvalues) ((energyBasis hH)ᴴ *ᵥ ψ) n := by
  change hH.eigenvectorBasis.repr (hilbertVector (H^n *ᵥ ψ)) = _
  rw [repr_hilbertVector]
  ext i
  have hp := congrFun (HermitianSpectralSupport.power_coordinates hH ψ n) i
  change ((energyBasis hH)ᴴ *ᵥ (H^n *ᵥ ψ)) i =
    ((OperatorBridge.hamiltonian hH.eigenvalues)^n *ᵥ ((energyBasis hH)ᴴ *ᵥ ψ)) i
  rw [OperatorBridge.hamiltonian,Matrix.diagonal_pow,Matrix.mulVec_diagonal]
  simpa only [mulVecLin_power,HermitianSpectralSupport.coordinateEquiv_apply,
    FiniteSpectralSupport.power_apply,Pi.pow_apply] using hp

lemma gs_coordinates {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (ψ : ι → ℂ) (n : ℕ) :
    hH.eigenvectorBasis.repr (gramSchmidtNormed ℂ (stateSequence H ψ) n) =
      gramSchmidtNormed ℂ (stateSequence (OperatorBridge.hamiltonian hH.eigenvalues)
        ((energyBasis hH)ᴴ *ᵥ ψ)) n := by
  rw [isometry_gramSchmidtNormed]
  congr 1
  funext k
  exact state_coordinates hH ψ k

lemma evolution_coordinates {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (ψ : ι → ℂ) (t : ℝ) :
    hH.eigenvectorBasis.repr (evolvedVector H ψ t) =
      evolvedVector (OperatorBridge.hamiltonian hH.eigenvalues) ((energyBasis hH)ᴴ *ᵥ ψ) t := by
  let c : ℂ := -((t:ℂ)*Complex.I)
  have he := exp_changeBasis (energyBasis hH) (c • H) (energyBasis_unitary hH)
  rw [changeBasis_smul,hamiltonian_coordinates hH] at he
  have he' : (energyBasis hH)ᴴ*NormedSpace.exp ℂ (c • H) =
      NormedSpace.exp ℂ (c • OperatorBridge.hamiltonian hH.eigenvalues)*(energyBasis hH)ᴴ := by
    rw [he]
    simp [changeBasis,mul_assoc,energyBasis_unitary_reverse hH]
  unfold evolvedVector
  rw [repr_hilbertVector]
  change hilbertVector ((energyBasis hH)ᴴ *ᵥ (NormedSpace.exp ℂ (c • H) *ᵥ ψ)) =
    hilbertVector (NormedSpace.exp ℂ (c • OperatorBridge.hamiltonian hH.eigenvalues) *ᵥ
      ((energyBasis hH)ᴴ *ᵥ ψ))
  rw [Matrix.mulVec_mulVec,he',← Matrix.mulVec_mulVec]

/-- One real orthonormal polynomial family simultaneously supplies the true
Krylov degrees, physical eigen-coordinates and spectral amplitudes for an
arbitrary finite Hermitian generator and arbitrary complex seed. -/
theorem spectral_data {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (ψ : ι → ℂ) :
    ∃ p : ℕ → Polynomial ℝ,
      (∀ n, (p n).degree ≤ (n : WithBot ℕ)) ∧
      (∀ n, gramSchmidtNormed ℂ (stateSequence H ψ) n ≠ 0 →
        (p n).degree = (n : WithBot ℕ)) ∧
      (∀ n, hH.eigenvectorBasis.repr (gramSchmidtNormed ℂ (stateSequence H ψ) n) =
        polynomialMap hH.eigenvalues ((energyBasis hH)ᴴ *ᵥ ψ) (p n)) ∧
      (∀ i j : GSIndex (stateSequence H ψ),
        weightedDot hH.eigenvalues ((energyBasis hH)ᴴ *ᵥ ψ) (p i.val) (p j.val) =
          if i=j then 1 else 0) ∧
      (∀ n t, ⟪gramSchmidtNormed ℂ (stateSequence H ψ) n,evolvedVector H ψ t⟫_ℂ =
        ∑ i, ((‖((energyBasis hH)ᴴ *ᵥ ψ) i‖^2*(p n).eval (hH.eigenvalues i) : ℝ) : ℂ)*
          OperatorBridge.phase (hH.eigenvalues i) t) := by
  classical
  obtain ⟨p,hd,he,hp,_,ha⟩ := physical_spectral_data hH.eigenvalues ((energyBasis hH)ᴴ *ᵥ ψ)
  have hc (n : ℕ) : hH.eigenvectorBasis.repr (gramSchmidtNormed ℂ (stateSequence H ψ) n) =
      polynomialMap hH.eigenvalues ((energyBasis hH)ᴴ *ᵥ ψ) (p n) := by
    rw [gs_coordinates,hp]
  refine ⟨p,hd,?_,hc,?_,?_⟩
  · intro n hn
    apply he n
    intro hz
    apply hn
    apply hH.eigenvectorBasis.repr.injective
    rw [gs_coordinates,hz,map_zero]
  · intro i j
    have hg := (orthonormal_iff_ite.mp (gramSchmidt_orthonormal' (stateSequence H ψ))) i j
    have ht := hH.eigenvectorBasis.repr.inner_map_map
      (gramSchmidtNormed ℂ (stateSequence H ψ) i.val)
      (gramSchmidtNormed ℂ (stateSequence H ψ) j.val)
    rw [hc i.val,hc j.val,polynomial_inner,hg] at ht
    by_cases hij : i=j <;> simpa [hij] using congrArg Complex.re ht
  · intro n t
    calc
      _ = ⟪hH.eigenvectorBasis.repr (gramSchmidtNormed ℂ (stateSequence H ψ) n),
        hH.eigenvectorBasis.repr (evolvedVector H ψ t)⟫_ℂ :=
          (hH.eigenvectorBasis.repr.inner_map_map _ _).symm
      _ = _ := by rw [gs_coordinates,evolution_coordinates]; exact ha n t

/-- Source eq:spectral-formula for every actual Hermitian state-chain degree,
with the true complex seed, actual normalized GS process and actual exponential.
The eigenbasis, real spectral polynomials and all transports are constructed,
not additional assumptions. -/
theorem spectral_amplitudes {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (ψ : ι → ℂ) :
    ∃ p : ℕ → Polynomial ℝ, ∀ n t,
      ⟪gramSchmidtNormed ℂ (stateSequence H ψ) n,evolvedVector H ψ t⟫_ℂ =
        ∑ i, ((‖((energyBasis hH)ᴴ *ᵥ ψ) i‖^2*(p n).eval (hH.eigenvalues i) : ℝ) : ℂ)*
          OperatorBridge.phase (hH.eigenvalues i) t := by
  obtain ⟨p,hp⟩ := physical_spectral_formula hH.eigenvalues ((energyBasis hH)ᴴ *ᵥ ψ)
  refine ⟨p,?_⟩
  intro n t
  calc
    _ = ⟪hH.eigenvectorBasis.repr (gramSchmidtNormed ℂ (stateSequence H ψ) n),
      hH.eigenvectorBasis.repr (evolvedVector H ψ t)⟫_ℂ :=
        (hH.eigenvectorBasis.repr.inner_map_map _ _).symm
    _ = _ := by rw [gs_coordinates,evolution_coordinates]; exact hp n t

/-- The weights of the actual normalized seed form a probability distribution,
even when eigenvalues repeat or some spectral coordinates vanish. -/
theorem spectral_weights_normalized {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ψ : ι → ℂ) (hψ : ‖hilbertVector ψ‖=1) :
    (∑ i,‖((energyBasis hH)ᴴ *ᵥ ψ) i‖^2)=1 := by
  apply weights_normalized
  rw [← repr_hilbertVector,hH.eigenvectorBasis.repr.norm_map,hψ]
end
end Krylov.HermitianSpectralFormula
