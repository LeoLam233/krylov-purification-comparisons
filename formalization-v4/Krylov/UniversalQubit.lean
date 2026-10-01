import Krylov.PhysicalQubit
import Krylov.PurifiedCovariance
import Krylov.ThreeAtomOperator

/-!
# Basis-independent bridges for the universal qubit hierarchy

All Hamiltonians, states, roots, and evolutions below are actual complex
matrices. Spectral coordinates are obtained from mathlib's Hermitian spectral
theorem, including repeated eigenvalues. No full-rank hypothesis is imposed.
-/
namespace Krylov.UniversalQubit
open Matrix OperatorBridge ConcreteChains UnitaryCovariance
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 2000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual unitary matrix supplied by the Hermitian spectral theorem. -/
def energyBasis {H : Operator ι} (hH : H.IsHermitian) : Operator ι :=
  hH.eigenvectorUnitary

theorem energyBasis_unitary {H : Operator ι} (hH : H.IsHermitian) :
    (energyBasis hH)ᴴ * energyBasis hH = 1 :=
  unitary.coe_star_mul_self hH.eigenvectorUnitary

theorem energyBasis_unitary_reverse {H : Operator ι} (hH : H.IsHermitian) :
    energyBasis hH * (energyBasis hH)ᴴ = 1 :=
  unitary.coe_mul_star_self hH.eigenvectorUnitary

theorem hamiltonian_coordinates {H : Operator ι} (hH : H.IsHermitian) :
    changeBasis (energyBasis hH) H = hamiltonian hH.eigenvalues :=
  hH.star_mul_self_mul_eq_diagonal

theorem changeBasis_posSemidef (Q : Operator ι) {ρ : Operator ι} (hρ : ρ.PosSemidef) :
    (changeBasis Q ρ).PosSemidef := hρ.conjTranspose_mul_mul_same Q

theorem changeBasis_trace (Q A : Operator ι) (hQ : Q * Qᴴ = 1) :
    trace (changeBasis Q A) = trace A := by
  unfold changeBasis
  rw [trace_mul_cycle, hQ, one_mul]

/-- Canonical positive square roots commute with unitary change of basis. -/
theorem sqrt_coordinates (Q : Operator ι) {ρ : Operator ι} (hρ : ρ.PosSemidef)
    (hQ : Q * Qᴴ = 1) :
    changeBasis Q hρ.sqrt = (changeBasis_posSemidef Q hρ).sqrt := by
  apply (changeBasis_posSemidef Q hρ.posSemidef_sqrt).eq_sqrt_of_sq_eq
  rw [pow_two, ← changeBasis_mul Q _ _ hQ, hρ.sqrt_mul_self]

/-- A row-vectorized purification keeps its original ancilla coordinates when
only the physical energy basis is changed. Its row weights are nevertheless
exactly the transformed density diagonal. -/
theorem physical_root_row_weights {n : ℕ} (Q : Operator (Fin n))
    {ρ : Operator (Fin n)} (hρ : ρ.PosSemidef) (i : Fin n) :
    Purification.rowWeight (Qᴴ * hρ.sqrt) i = (changeBasis Q ρ i i).re := by
  rw [Purification.rowWeight_eq_density_diagonal]
  congr 2
  simp only [conjTranspose_mul, conjTranspose_conjTranspose,
    hρ.posSemidef_sqrt.isHermitian.eq, changeBasis, mul_assoc]
  rw [← mul_assoc hρ.sqrt hρ.sqrt, hρ.sqrt_mul_self]

/-- Exact scalar probability transport for arbitrary Hermitian matrices. -/
theorem original_probability {H : Operator ι} (hH : H.IsHermitian)
    (A v : Operator ι) (t : ℝ) :
    matrixProbability H A (changeBasis (energyBasis hH)ᴴ v) t =
      chainProbability hH.eigenvalues (changeBasis (energyBasis hH) A) v t := by
  rw [← matrixProbability_changeBasis (energyBasis hH) _ _ _ t
    (energyBasis_unitary hH) (energyBasis_unitary_reverse hH)]
  rw [hamiltonian_coordinates hH,
    changeBasis_inverse _ _ (energyBasis_unitary hH), diagonal_probability]

/-- Transport includes the actual canonical square root, rather than an
independently chosen purification amplitude. -/
theorem original_spread_probability {H ρ : Operator ι} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (v : Operator ι) (t : ℝ) :
    matrixProbability H hρ.sqrt (changeBasis (energyBasis hH)ᴴ v) t =
      chainProbability hH.eigenvalues (changeBasis_posSemidef (energyBasis hH) hρ).sqrt v t := by
  rw [original_probability hH, sqrt_coordinates _ hρ (energyBasis_unitary_reverse hH)]

/-- Exact lifted-Hamiltonian probability transport for the original canonical
rank-one I-purified density. -/
theorem original_purified_probability {n : ℕ} {H ρ : Operator (Fin n)}
    (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (v : Operator (Fin n × Fin n)) (t : ℝ) :
    matrixProbability (PurifiedCovariance.lift H) (Purification.pureSeed hρ.sqrt)
      (changeBasis (PurifiedCovariance.lift (energyBasis hH))ᴴ v) t =
      chainProbability (fun a : Fin n × Fin n => hH.eigenvalues a.1)
        (Purification.pureSeed ((energyBasis hH)ᴴ * hρ.sqrt)) v t := by
  rw [← matrixProbability_changeBasis (PurifiedCovariance.lift (energyBasis hH)) _ _ _ t
    (PurifiedCovariance.lift_unitary _ (energyBasis_unitary hH))
    (PurifiedCovariance.lift_unitary_reverse _ (energyBasis_unitary_reverse hH))]
  rw [PurifiedCovariance.lift_changeBasis, hamiltonian_coordinates hH,
    PurifiedCovariance.lift_diagonal, PurifiedCovariance.pureSeed_changeBasis,
    changeBasis_inverse _ _ (PurifiedCovariance.lift_unitary _ (energyBasis_unitary hH)),
    diagonal_probability]

/-- Three gap weights including the stationary zero-mass endpoint. -/
structure ThreeWeights (E : ι → ℝ) (A : Operator ι) (μ s : ℝ) : Prop where
  scale_pos : 0 < s
  mass_nonneg : 0 ≤ μ
  mass_lt : μ < 1
  support : ∀ i j, A i j ≠ 0 → E i - E j = -1 ∨ E i - E j = 0 ∨ E i - E j = 1
  weight_neg : gapWeight E A (-1) = s * μ / 2
  weight_zero : gapWeight E A 0 = s * (1 - μ)
  weight_pos : gapWeight E A 1 = s * μ / 2

namespace ThreeWeights
variable {E : ι → ℝ} {A : Operator ι} {μ s : ℝ}

theorem data (h : ThreeWeights E A μ s) (hm : 0 < μ) :
    ThreeAtomOperator.Data E A μ s :=
  ⟨h.scale_pos, hm, h.mass_lt, h.support, h.weight_neg, h.weight_zero, h.weight_pos⟩

theorem inner_filters (h : ThreeWeights E A μ s) (f g : ℝ → ℂ) :
    hsInner (spectralFilter E f A) (spectralFilter E g A) =
      (s * μ / 2 : ℝ) * star (f (-1)) * g (-1) +
      (s * (1 - μ) : ℝ) * star (f 0) * g 0 +
      (s * μ / 2 : ℝ) * star (f 1) * g 1 := by
  have hsupp : ∀ i j, A i j ≠ 0 → E i - E j ∈ ({-1,0,1} : Finset ℝ) := by
    intro i j hn
    rcases h.support i j hn with ha | ha | ha <;> simp [ha]
  rw [hsInner_filters_supported E f g A {-1,0,1} hsupp]
  norm_num [h.weight_neg, h.weight_zero, h.weight_pos]
  ring

theorem gram (h : ThreeWeights E A μ s) (k l : Fin 3) :
    hsInner (ThreeAtomOperator.chain E A μ k) (ThreeAtomOperator.chain E A μ l) =
      if k = l then ((s * ThreeAtomOperator.norms μ k : ℝ) : ℂ) else 0 := by
  simp only [ThreeAtomOperator.chain, polynomial_eq_spectralFilter]
  rw [inner_filters h]
  fin_cases k <;> fin_cases l <;>
    norm_num [ThreeAtomOperator.polynomial, ThreeAtomOperator.norms, Complex.star_def] <;> ring

/-- Degenerate μ=0 chains carry zero complexity exactly; no limiting argument
or nonzero-coherence assumption is used. -/
theorem complexity_eq (h : ThreeWeights E A μ s) (t : ℝ) :
    chainComplexity E A (ThreeAtomOperator.chain E A μ) t = Qubit.threeAtom μ t := by
  rcases h.mass_nonneg.eq_or_lt with hm | hm
  · subst μ
    simp only [chainComplexity, chainProbability, gram h]
    norm_num [Fin.sum_univ_succ, ThreeAtomOperator.norms, Qubit.threeAtom]
  · exact ThreeAtomOperator.complexity_eq_threeAtom (h.data hm) t

end ThreeWeights

/-- Only energy differences matter, and an arbitrary real energy gap is an
exact rescaling of physical time. Includes a zero or negative gap. -/
theorem diagonal_evolution_affine (E : ι → ℝ) (a b t : ℝ) (A : Operator ι) :
    diagonalUnitary (fun i => a + b * E i) t * A *
      (diagonalUnitary (fun i => a + b * E i) t)ᴴ =
      diagonalUnitary E (b*t) * A * (diagonalUnitary E (b*t))ᴴ := by
  rw [diagonalUnitary_conjugation, diagonalUnitary_conjugation]
  ext i j
  simp only [spectralFilter, phase]
  congr 2
  push_cast
  ring

theorem chainProbability_affine (E : ι → ℝ) (a b t : ℝ) (A v : Operator ι) :
    chainProbability (fun i => a + b * E i) A v t = chainProbability E A v (b*t) := by
  simp only [chainProbability, diagonal_evolution_affine]

/-- The two-level reference energy labels are used only for the chain's
coordinates; actual evolution retains the original Hamiltonian. -/
def referenceEnergy : Fin 2 → ℝ := ![0,1]

theorem energy_affine (E : Fin 2 → ℝ) :
    E = fun i => E 0 + (E 1 - E 0) * referenceEnergy i := by
  funext i; fin_cases i <;> simp [referenceEnergy]

theorem qubitProbability_rescale (E : Fin 2 → ℝ) (A v : Operator (Fin 2)) (t : ℝ) :
    chainProbability E A v t =
      chainProbability referenceEnergy A v ((E 1-E 0)*t) := by
  conv_lhs => rw [energy_affine E]
  exact chainProbability_affine _ _ _ _ _ _

theorem liftedProbability_rescale (E : Fin 2 → ℝ)
    (A v : Operator (Fin 2 × Fin 2)) (t : ℝ) :
    chainProbability (fun i : Fin 2 × Fin 2 => E i.1) A v t =
      chainProbability (fun i : Fin 2 × Fin 2 => referenceEnergy i.1) A v ((E 1-E 0)*t) := by
  have he : (fun i : Fin 2 × Fin 2 => E i.1) =
      fun i : Fin 2 × Fin 2 => E 0 + (E 1-E 0)*referenceEnergy i.1 := by
    funext i; exact congrFun (energy_affine E) i.1
  rw [he]
  exact chainProbability_affine _ _ _ _ _ _

open PhysicalQubit

private theorem reference_support (i j : Fin 2) :
    referenceEnergy i - referenceEnergy j = -1 ∨
      referenceEnergy i - referenceEnergy j = 0 ∨
      referenceEnergy i - referenceEnergy j = 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [referenceEnergy]

private theorem reference_distinct : referenceEnergy 0 ≠ referenceEnergy 1 := by
  norm_num [referenceEnergy]

theorem spread_weights {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ThreeWeights referenceEnergy hρ.sqrt (spreadCoefficient ρ hρ) 1 := by
  obtain ⟨hs, hsk, hki, hi⟩ := coefficient_hierarchy hρ htr
  have htab := spread_gap_table hρ htr referenceEnergy reference_distinct
  refine ⟨by norm_num, hs, by linarith, fun i j _ => reference_support i j, ?_, ?_, ?_⟩
  · simpa [gapNodes, referenceEnergy, threeAtomWeights] using congrFun htab 0
  · simpa [gapNodes, referenceEnergy, threeAtomWeights] using congrFun htab 1
  · simpa [gapNodes, referenceEnergy, threeAtomWeights] using congrFun htab 2

theorem mixed_weights {ρ : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ThreeWeights referenceEnergy ρ (mixedCoefficient ρ) (purity ρ) := by
  obtain ⟨hs, hsk, hki, hi⟩ := coefficient_hierarchy hρ htr
  have hp : 0 < purity ρ := by have := (purity_bounds hρ htr).1; linarith
  have htab := mixed_gap_table hρ htr referenceEnergy reference_distinct
  refine ⟨hp, by linarith, by linarith, fun i j _ => reference_support i j, ?_, ?_, ?_⟩
  · have hw : gapWeight referenceEnergy ρ (-1) / purity ρ = mixedCoefficient ρ / 2 := by
      simpa [gapNodes, referenceEnergy, threeAtomWeights] using congrFun htab (0 : Fin 3)
    have := (div_eq_iff hp.ne').mp hw
    linarith
  · have hw := congrFun htab 1
    simp only [gapNodes, threeAtomWeights, Matrix.cons_val_one, Matrix.cons_val_zero] at hw
    exact (div_eq_iff hp.ne').mp hw |>.trans (mul_comm _ _)
  · have hw : gapWeight referenceEnergy ρ 1 / purity ρ = mixedCoefficient ρ / 2 := by
      simpa [gapNodes, referenceEnergy, threeAtomWeights] using congrFun htab (2 : Fin 3)
    have := (div_eq_iff hp.ne').mp hw
    linarith

/-- The actual purified matrix's full gap measure depends only on its density
row weights; this handles the unchanged ancilla coordinates exactly. -/
theorem purified_weights {ρ S : QubitMatrix} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hrow : ∀ i, Purification.rowWeight S i = (ρ i i).re) :
    ThreeWeights (fun i : Fin 2 × Fin 2 => referenceEnergy i.1)
      (Purification.pureSeed S) (purifiedCoefficient ρ) 1 := by
  obtain ⟨hs, hsk, hki, hi⟩ := coefficient_hierarchy hρ htr
  have hgap : ∀ ω,
      gapWeight (fun i : Fin 2 × Fin 2 => referenceEnergy i.1)
        (Purification.pureSeed S) ω =
      Purification.pureGapWeight referenceEnergy hρ.sqrt ω := by
    intro ω
    change Purification.pureGapWeight referenceEnergy S ω = _
    simp only [Purification.pure_gap_difference_convolution, hrow, sqrt_row_weight hρ]
  have htab := purified_gap_table hρ htr referenceEnergy reference_distinct
  refine ⟨by norm_num, by linarith, by linarith,
    fun i j _ => reference_support i.1 j.1, ?_, ?_, ?_⟩
  · rw [hgap]
    simpa [gapNodes, referenceEnergy, threeAtomWeights] using congrFun htab 0
  · rw [hgap]
    simpa [gapNodes, referenceEnergy, threeAtomWeights] using congrFun htab 1
  · rw [hgap]
    simpa [gapNodes, referenceEnergy, threeAtomWeights] using congrFun htab 2

/-- Index-weighted probabilities of actual matrix-exponential evolution. -/
def matrixComplexity {m : ℕ} (H A : Operator ι) (v : Fin m → Operator ι) (t : ℝ) : ℝ :=
  ∑ k, (k.val : ℝ) * matrixProbability H A (v k) t

/-- A one-vector stationary chain, zero-padded to keep the ambient index set fixed. -/
def stationaryChain (A : Operator ι) (k : Fin 3) : Operator ι := if k=0 then A else 0

theorem matrixProbability_zero (H A : Operator ι) (t : ℝ) :
    matrixProbability H A 0 t = 0 := by
  simp [matrixProbability, hsInner]

theorem stationary_complexity (H A : Operator ι) (t : ℝ) :
    matrixComplexity H A (stationaryChain A) t = 0 := by
  simp [matrixComplexity, stationaryChain, Fin.sum_univ_succ, matrixProbability_zero]

def coordinateDensity {H : QubitMatrix} (hH : H.IsHermitian) (ρ : QubitMatrix) : QubitMatrix :=
  changeBasis (energyBasis hH) ρ

theorem coordinateDensity_posSemidef {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) : (coordinateDensity hH ρ).PosSemidef :=
  changeBasis_posSemidef _ hρ

theorem coordinateDensity_trace {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (htr : ρ.trace = 1) : (coordinateDensity hH ρ).trace = 1 := by
  rw [coordinateDensity, changeBasis_trace _ _ (energyBasis_unitary_reverse hH), htr]

def energyGap {H : QubitMatrix} (hH : H.IsHermitian) : ℝ := hH.eigenvalues 1 - hH.eigenvalues 0

def spreadChain {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (k : Fin 3) : QubitMatrix :=
  if energyGap hH = 0 then stationaryChain hρ.sqrt k else
    changeBasis (energyBasis hH)ᴴ
      (ThreeAtomOperator.chain referenceEnergy (coordinateDensity_posSemidef hH hρ).sqrt
        (spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ)) k)

def mixedChain {H : QubitMatrix} (hH : H.IsHermitian) (ρ : QubitMatrix)
    (k : Fin 3) : QubitMatrix :=
  if energyGap hH = 0 then stationaryChain ρ k else
    changeBasis (energyBasis hH)ᴴ
      (ThreeAtomOperator.chain referenceEnergy (coordinateDensity hH ρ)
        (mixedCoefficient (coordinateDensity hH ρ)) k)

def purifiedChain {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (k : Fin 3) : Operator (Fin 2 × Fin 2) :=
  if energyGap hH = 0 then stationaryChain (Purification.pureSeed hρ.sqrt) k else
    changeBasis (PurifiedCovariance.lift (energyBasis hH))ᴴ
      (ThreeAtomOperator.chain (fun i : Fin 2 × Fin 2 => referenceEnergy i.1)
        (Purification.pureSeed ((energyBasis hH)ᴴ * hρ.sqrt))
        (purifiedCoefficient (coordinateDensity hH ρ)) k)

/-- Physical square-root spread in a complete ordered chain, with zero padding
at stationary endpoints. -/
def spread {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (t : ℝ) : ℝ :=
  matrixComplexity H hρ.sqrt (spreadChain hH hρ) t

/-- Physical mixed-density operator complexity. -/
def mixed {H : QubitMatrix} (hH : H.IsHermitian) (ρ : QubitMatrix) (t : ℝ) : ℝ :=
  matrixComplexity H ρ (mixedChain hH ρ) t

/-- Physical I-purified operator complexity for the canonical root vector. -/
def purified {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (t : ℝ) : ℝ :=
  matrixComplexity (PurifiedCovariance.lift H) (Purification.pureSeed hρ.sqrt)
    (purifiedChain hH hρ) t

theorem spread_eq {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (t : ℝ) :
    spread hH hρ t =
      Qubit.threeAtom (spreadCoefficient (coordinateDensity hH ρ)
        (coordinateDensity_posSemidef hH hρ)) (energyGap hH * t) := by
  by_cases hg : energyGap hH = 0
  · have hc : spreadChain hH hρ = stationaryChain hρ.sqrt := by
      funext k; simp only [spreadChain, hg, ↓reduceIte]
    rw [spread, hc, stationary_complexity, hg]
    simp [Qubit.threeAtom]
  · simp only [spread, matrixComplexity, spreadChain, hg, ↓reduceIte]
    have hr : ∀ k : Fin 3,
        matrixProbability H hρ.sqrt
          (changeBasis (energyBasis hH)ᴴ
            (ThreeAtomOperator.chain referenceEnergy (coordinateDensity_posSemidef hH hρ).sqrt
              (spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ)) k)) t =
        chainProbability referenceEnergy (coordinateDensity_posSemidef hH hρ).sqrt
          (ThreeAtomOperator.chain referenceEnergy (coordinateDensity_posSemidef hH hρ).sqrt
            (spreadCoefficient (coordinateDensity hH ρ) (coordinateDensity_posSemidef hH hρ)) k)
          (energyGap hH*t) := by
      intro k; rw [original_spread_probability, qubitProbability_rescale]; rfl
    simp only [hr]
    exact ThreeWeights.complexity_eq
      (spread_weights (coordinateDensity_posSemidef hH hρ) (coordinateDensity_trace hH htr)) _

theorem mixed_eq {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (t : ℝ) :
    mixed hH ρ t =
      Qubit.threeAtom (mixedCoefficient (coordinateDensity hH ρ)) (energyGap hH * t) := by
  by_cases hg : energyGap hH = 0
  · have hc : mixedChain hH ρ = stationaryChain ρ := by
      funext k; simp only [mixedChain, hg, ↓reduceIte]
    rw [mixed, hc, stationary_complexity, hg]
    simp [Qubit.threeAtom]
  · simp only [mixed, matrixComplexity, mixedChain, hg, ↓reduceIte]
    have hr : ∀ k : Fin 3,
        matrixProbability H ρ
          (changeBasis (energyBasis hH)ᴴ
            (ThreeAtomOperator.chain referenceEnergy (coordinateDensity hH ρ)
              (mixedCoefficient (coordinateDensity hH ρ)) k)) t =
        chainProbability referenceEnergy (coordinateDensity hH ρ)
          (ThreeAtomOperator.chain referenceEnergy (coordinateDensity hH ρ)
            (mixedCoefficient (coordinateDensity hH ρ)) k) (energyGap hH*t) := by
      intro k; rw [original_probability, qubitProbability_rescale]; rfl
    simp only [hr]
    exact ThreeWeights.complexity_eq
      (mixed_weights (coordinateDensity_posSemidef hH hρ) (coordinateDensity_trace hH htr)) _

theorem purified_eq {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (t : ℝ) :
    purified hH hρ t =
      Qubit.threeAtom (purifiedCoefficient (coordinateDensity hH ρ)) (energyGap hH * t) := by
  by_cases hg : energyGap hH = 0
  · have hc : purifiedChain hH hρ = stationaryChain (Purification.pureSeed hρ.sqrt) := by
      funext k; simp only [purifiedChain, hg, ↓reduceIte]
    rw [purified, hc, stationary_complexity, hg]
    simp [Qubit.threeAtom]
  · simp only [purified, matrixComplexity, purifiedChain, hg, ↓reduceIte]
    have hr : ∀ k : Fin 3,
        matrixProbability (PurifiedCovariance.lift H) (Purification.pureSeed hρ.sqrt)
          (changeBasis (PurifiedCovariance.lift (energyBasis hH))ᴴ
            (ThreeAtomOperator.chain (fun i : Fin 2 × Fin 2 => referenceEnergy i.1)
              (Purification.pureSeed ((energyBasis hH)ᴴ*hρ.sqrt))
              (purifiedCoefficient (coordinateDensity hH ρ)) k)) t =
        chainProbability (fun i : Fin 2 × Fin 2 => referenceEnergy i.1)
          (Purification.pureSeed ((energyBasis hH)ᴴ*hρ.sqrt))
          (ThreeAtomOperator.chain (fun i : Fin 2 × Fin 2 => referenceEnergy i.1)
            (Purification.pureSeed ((energyBasis hH)ᴴ*hρ.sqrt))
            (purifiedCoefficient (coordinateDensity hH ρ)) k) (energyGap hH*t) := by
      intro k; rw [original_purified_probability, liftedProbability_rescale]; rfl
    simp only [hr]
    exact ThreeWeights.complexity_eq
      (purified_weights (coordinateDensity_posSemidef hH hρ) (coordinateDensity_trace hH htr)
        (physical_root_row_weights (energyBasis hH) hρ)) _

/-- The universal all-time physical qubit hierarchy for every Hermitian
Hamiltonian and every PSD unit-trace density matrix, including all rank,
coherence, spectral-degeneracy, and time endpoints. -/
theorem hierarchy {H ρ : QubitMatrix} (hH : H.IsHermitian) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (t : ℝ) :
    spread hH hρ t ≤ mixed hH ρ t ∧ mixed hH ρ t ≤ purified hH hρ t := by
  rw [spread_eq hH hρ htr, mixed_eq hH hρ htr, purified_eq hH hρ htr]
  exact density_formula_hierarchy (coordinateDensity_posSemidef hH hρ)
    (coordinateDensity_trace hH htr) (energyGap hH) t

/-! ## Certification of the physical ordered chains -/

/-- The original Hamiltonian's actual commutator. -/
def matrixCommutator (H : Operator ι) : Module.End ℂ (Operator ι) :=
  LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H

@[simp] theorem matrixCommutator_apply (H A : Operator ι) :
    matrixCommutator H A = H*A-A*H := rfl

theorem changeBasis_injective (Q : Operator ι) (hQ : Q*Qᴴ=1) :
    Function.Injective (changeBasis Q) := by
  intro A B he
  have hh := congrArg (changeBasis Qᴴ) he
  have hi (C : Operator ι) : changeBasis Qᴴ (changeBasis Q C) = C := by
    simpa only [conjTranspose_conjTranspose] using
      changeBasis_inverse Qᴴ C (by simpa only [conjTranspose_conjTranspose] using hQ)
  simpa only [hi] using hh

theorem liouvillian_affine (E : ι → ℝ) (a b : ℝ) (A : Operator ι) :
    liouvillian (fun i => a+b*E i) A = (b : ℂ) • liouvillian E A := by
  ext i j
  change (((a+b*E i)-(a+b*E j) : ℝ) : ℂ) * A i j =
    (b : ℂ) * (((E i-E j : ℝ) : ℂ) * A i j)
  push_cast
  ring

/-- Exact intertwining with the original commutator, including a zero gap. -/
theorem commutator_transport (Q H : Operator ι) (E : ι → ℝ) (a b : ℝ)
    (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1)
    (hH : changeBasis Q H = hamiltonian (fun i => a+b*E i)) (A : Operator ι) :
    matrixCommutator H (changeBasis Qᴴ A) =
      (b : ℂ) • changeBasis Qᴴ (liouvillian E A) := by
  apply changeBasis_injective Q hQ'
  rw [matrixCommutator_apply, changeBasis_commutator Q H _ hQ', hH,
    changeBasis_inverse _ _ hQ, ← liouvillian_commutator, liouvillian_affine,
    changeBasis_smul, changeBasis_inverse _ _ hQ]

namespace ThreeWeights
variable {E : ι → ℝ} {A : Operator ι} {μ s : ℝ}

/-- The ordered recurrence holds at the zero-mass endpoint as well. -/
theorem ordered_recurrence (h : ThreeWeights E A μ s) (k : Fin 3) :
    liouvillian E (ThreeAtomOperator.chain E A μ k) =
      (if hk : k.val + 1 < 3 then ThreeAtomOperator.chain E A μ ⟨k.val + 1,hk⟩ else 0) +
      (if hk : 0 < k.val then
        (ThreeAtomOperator.bSquared μ k : ℂ) • ThreeAtomOperator.chain E A μ ⟨k.val - 1, by omega⟩ else 0) := by
  ext i j
  by_cases hz : A i j = 0
  · fin_cases k <;> simp [liouvillian, ThreeAtomOperator.chain_entry, ThreeAtomOperator.polynomial, hz]
  · change ((E i - E j : ℝ) : ℂ) * ThreeAtomOperator.chain E A μ k i j = _
    rcases h.support i j hz with hg | hg | hg <;>
      rw [hg] <;> fin_cases k <;>
      simp [ThreeAtomOperator.chain_entry, ThreeAtomOperator.polynomial, ThreeAtomOperator.bSquared, hg] <;> ring

end ThreeWeights

/-- The cyclic span is invariant under its generating endomorphism. -/
theorem cyclicSpan_invariant {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : Module.End ℂ M) (A : M) (x : M) (hx : x ∈ cyclicSpan L A) :
    L x ∈ cyclicSpan L A := by
  apply span_range_invariant L (fun k : ℕ => (L^k) A) ?_ x hx
  intro k
  exact Submodule.subset_span ⟨k+1, by simp only [pow_succ', Module.End.mul_apply]⟩

/-- A nonzero frequency-rescaling of an ordered three-term chain preserves
its complete cyclic Krylov span. Zero terminal vectors are permitted. -/
theorem span_three_chain_eq_cyclic {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : Module.End ℂ M) (A : M) (v : Fin 3 → M) (b μ : ℂ) (hb : b ≠ 0)
    (h0 : v 0 = A)
    (hL0 : L (v 0) = b • v 1)
    (hL1 : L (v 1) = b • v 2 + (b*μ) • v 0)
    (hL2 : L (v 2) = (b*(1-μ)) • v 1) :
    Submodule.span ℂ (Set.range v) = cyclicSpan L A := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    have hv0 : v 0 ∈ cyclicSpan L A := by
      rw [h0]
      exact Submodule.subset_span ⟨0, by simp⟩
    have hv1 : v 1 ∈ cyclicSpan L A := by
      have hi := cyclicSpan_invariant L A _ hv0
      rw [hL0] at hi
      exact (cyclicSpan L A).smul_mem_iff hb |>.mp hi
    have hv2 : v 2 ∈ cyclicSpan L A := by
      have hi := cyclicSpan_invariant L A _ hv1
      rw [hL1] at hi
      have hh := (cyclicSpan L A).sub_mem hi ((cyclicSpan L A).smul_mem (b*μ) hv0)
      simp only [add_sub_cancel_right] at hh
      exact (cyclicSpan L A).smul_mem_iff hb |>.mp hh
    rintro _ ⟨k,rfl⟩
    fin_cases k <;> assumption
  · apply cyclicSpan_le_of_invariant L A _
    · rw [← h0]; exact Submodule.subset_span ⟨0,rfl⟩
    · apply span_range_invariant
      intro k
      have hv : ∀ j : Fin 3, v j ∈ Submodule.span ℂ (Set.range v) :=
        fun j => Submodule.subset_span ⟨j,rfl⟩
      fin_cases k
      · change L (v 0) ∈ _
        rw [hL0]; exact Submodule.smul_mem _ _ (hv 1)
      · change L (v 1) ∈ _
        rw [hL1]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hv 2)) (Submodule.smul_mem _ _ (hv 0))
      · change L (v 2) ∈ _
        rw [hL2]; exact Submodule.smul_mem _ _ (hv 1)

/-- A complete ordered, orthogonal three-term Krylov chain. If μ=0 only the
initial vector survives; the remaining two entries are zero padding. The
frequency b may have either sign because harmless Lanczos-vector phases do
not change normalized probabilities. -/
structure PaddedLanczos (H A : Operator ι) (v : Fin 3 → Operator ι) (μ s b : ℝ) : Prop where
  scale_pos : 0 < s
  mass_nonneg : 0 ≤ μ
  mass_lt : μ < 1
  seed : v 0 = A
  gram : ∀ k l, hsInner (v k) (v l) =
    if k=l then ((s * ThreeAtomOperator.norms μ k : ℝ) : ℂ) else 0
  step_zero : matrixCommutator H (v 0) = (b : ℂ) • v 1
  step_one : matrixCommutator H (v 1) =
    (b : ℂ) • v 2 + ((b : ℂ)*(μ : ℂ)) • v 0
  step_two : matrixCommutator H (v 2) = ((b : ℂ)*(1-(μ : ℂ))) • v 1
  complete : Submodule.span ℂ (Set.range v) = cyclicSpan (matrixCommutator H) A

def transportedChain (Q : Operator ι) (E : ι → ℝ) (A : Operator ι) (μ : ℝ)
    (k : Fin 3) : Operator ι := changeBasis Qᴴ (ThreeAtomOperator.chain E A μ k)

theorem transported_certificate (Q H : Operator ι) (E : ι → ℝ) (a b μ s : ℝ)
    (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1)
    (hH : changeBasis Q H = hamiltonian (fun i => a+b*E i))
    (A : Operator ι) (h : ThreeWeights E A μ s) (hb : b ≠ 0) :
    PaddedLanczos H (changeBasis Qᴴ A) (transportedChain Q E A μ) μ s b := by
  have h0 : transportedChain Q E A μ 0 = changeBasis Qᴴ A := by
    rw [transportedChain, ThreeAtomOperator.chain_zero]
  have hL0 : matrixCommutator H (transportedChain Q E A μ 0) =
      (b : ℂ) • transportedChain Q E A μ 1 := by
    rw [transportedChain, commutator_transport Q H E a b hQ hQ' hH,
      h.ordered_recurrence 0]
    simp [transportedChain]
  have hL1 : matrixCommutator H (transportedChain Q E A μ 1) =
      (b : ℂ) • transportedChain Q E A μ 2 +
        ((b : ℂ)*(μ : ℂ)) • transportedChain Q E A μ 0 := by
    rw [transportedChain, commutator_transport Q H E a b hQ hQ' hH,
      h.ordered_recurrence 1]
    simp [transportedChain, ThreeAtomOperator.bSquared, changeBasis, mul_add, add_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
    norm_cast
  have hL2 : matrixCommutator H (transportedChain Q E A μ 2) =
      ((b : ℂ)*(1-(μ : ℂ))) • transportedChain Q E A μ 1 := by
    rw [transportedChain, commutator_transport Q H E a b hQ hQ' hH,
      h.ordered_recurrence 2]
    simp [transportedChain, ThreeAtomOperator.bSquared, changeBasis,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  refine ⟨h.scale_pos, h.mass_nonneg, h.mass_lt, h0, ?_, hL0, hL1, hL2, ?_⟩
  · intro k l
    rw [transportedChain, transportedChain, hsInner_changeBasis Qᴴ _ _ (by simpa using hQ)]
    exact h.gram k l
  · exact span_three_chain_eq_cyclic _ _ _ (b : ℂ) (μ : ℂ)
      (Complex.ofReal_ne_zero.mpr hb) h0 hL0 hL1 hL2

theorem stationary_certificate (H A : Operator ι) (s : ℝ) (hs : 0 < s)
    (hn : hsInner A A = (s : ℂ)) (hc : matrixCommutator H A = 0) :
    PaddedLanczos H A (stationaryChain A) 0 s 0 := by
  have hz : matrixCommutator H (0 : Operator ι) = 0 := map_zero _
  refine ⟨hs, by norm_num, by norm_num, by simp [stationaryChain], ?_, ?_, ?_, ?_, ?_⟩
  · intro k l
    fin_cases k <;> fin_cases l <;> simp [stationaryChain, ThreeAtomOperator.norms, hsInner, hn]
    simpa only [hsInner] using hn
  · simpa [stationaryChain] using hc
  · simp [stationaryChain]
  · simp [stationaryChain]
  · apply span_three_chain_eq_cyclic _ _ _ (1 : ℂ) 0 one_ne_zero
    · simp [stationaryChain]
    · simpa [stationaryChain] using hc
    · simp [stationaryChain]
    · simp [stationaryChain]

theorem hsInner_self_zero {A : Operator ι} (h : hsInner A A = 0) : A = 0 := by
  have hd : star (Function.uncurry A) ⬝ᵥ Function.uncurry A = 0 := by
    simpa only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, hsInner, Function.uncurry_apply_pair] using h
  have hz := dotProduct_star_self_eq_zero.mp hd
  ext i j
  exact congrFun hz (i,j)

namespace PaddedLanczos
variable {H A : Operator ι} {v : Fin 3 → Operator ι} {μ s b : ℝ}

theorem seed_norm (h : PaddedLanczos H A v μ s b) : hsInner A A = (s : ℂ) := by
  have hh := h.gram 0 0
  simpa [h.seed, ThreeAtomOperator.norms] using hh

theorem seed_nonzero (h : PaddedLanczos H A v μ s b) : A ≠ 0 := by
  intro hz
  have hn := h.seed_norm
  simp [hz, hsInner] at hn
  exact h.scale_pos.ne' (Complex.ofReal_eq_zero.mp hn.symm)

theorem zero_mass_padding (h : PaddedLanczos H A v 0 s b) : v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · apply hsInner_self_zero
    simpa [ThreeAtomOperator.norms] using h.gram 1 1
  · apply hsInner_self_zero
    simpa [ThreeAtomOperator.norms] using h.gram 2 2

/-- The exact cyclic dimension, with a genuine one-dimensional stationary
chain at zero mass and no holes in the surviving Lanczos basis. -/
theorem cyclic_dimension (h : PaddedLanczos H A v μ s b) :
    Module.finrank ℂ (cyclicSpan (matrixCommutator H) A) = if μ=0 then 1 else 3 := by
  rw [← h.complete]
  by_cases hm : μ=0
  · subst μ
    rw [if_pos rfl]
    obtain ⟨h1,h2⟩ := h.zero_mass_padding
    have he : Submodule.span ℂ (Set.range v) = Submodule.span ℂ ({A} : Set (Operator ι)) := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨k,rfl⟩
        fin_cases k
        · change v 0 ∈ _
          rw [h.seed]; exact Submodule.subset_span (Set.mem_singleton A)
        · change v 1 ∈ _
          rw [h1]; exact Submodule.zero_mem _
        · change v 2 ∈ _
          rw [h2]; exact Submodule.zero_mem _
      · apply Submodule.span_le.mpr
        intro x hx
        have hx' : x=A := Set.mem_singleton_iff.mp hx
        subst x
        exact Submodule.subset_span ⟨0,h.seed⟩
    rw [he]
    exact finrank_span_singleton h.seed_nonzero
  · rw [if_neg hm]
    have hp : 0 < μ := lt_of_le_of_ne h.mass_nonneg (Ne.symm hm)
    have hli : LinearIndependent ℂ v := by
      apply linearIndependent_of_hsGram v (fun k => (s * ThreeAtomOperator.norms μ k : ℝ)) h.gram
      intro k
      apply Complex.ofReal_ne_zero.mpr
      have hs := h.scale_pos
      have h1 : 0 < 1-μ := sub_pos.mpr h.mass_lt
      have hpos : 0 < s * ThreeAtomOperator.norms μ k := by
        fin_cases k <;> simp [ThreeAtomOperator.norms] <;> positivity
      exact hpos.ne'
    simpa using finrank_span_eq_card hli

end PaddedLanczos

/-- General physical-basis chain construction used by all three seeds. -/
def physicalChain (Q : Operator ι) (E : ι → ℝ) (A Aref : Operator ι) (μ b : ℝ)
    (k : Fin 3) : Operator ι :=
  if b=0 then stationaryChain A k else transportedChain Q E Aref μ k

theorem physical_certificate (Q H : Operator ι) (E : ι → ℝ) (a b μ s : ℝ)
    (hQ : Qᴴ*Q=1) (hQ' : Q*Qᴴ=1)
    (hH : changeBasis Q H = hamiltonian (fun i => a+b*E i))
    (A Aref : Operator ι) (hA : changeBasis Q A = Aref)
    (h : ThreeWeights E Aref μ s) :
    PaddedLanczos H A (physicalChain Q E A Aref μ b) (if b=0 then 0 else μ) s b := by
  have hi : changeBasis Qᴴ Aref = A := by
    rw [← hA]
    simpa only [conjTranspose_conjTranspose] using
      changeBasis_inverse Qᴴ A (by simpa only [conjTranspose_conjTranspose] using hQ')
  by_cases hb : b=0
  · subst b
    have hv : physicalChain Q E A Aref μ 0 = stationaryChain A := by
      funext k; simp [physicalChain]
    rw [hv, if_pos rfl]
    apply stationary_certificate H A s h.scale_pos
    · have hn := h.gram 0 0
      rw [ThreeAtomOperator.chain_zero] at hn
      have hn' : hsInner Aref Aref = (s : ℂ) := by simpa [ThreeAtomOperator.norms] using hn
      rw [← hA, hsInner_changeBasis Q A A hQ'] at hn'
      exact hn'
    · rw [← hi, commutator_transport Q H E a 0 hQ hQ' hH]
      simp
  · have hv : physicalChain Q E A Aref μ b = transportedChain Q E Aref μ := by
      funext k; simp [physicalChain, hb]
    rw [hv, if_neg hb, ← hi]
    exact transported_certificate Q H E a b μ s hQ hQ' hH Aref h hb

private theorem qubit_hamiltonian_affine {H : QubitMatrix} (hH : H.IsHermitian) :
    changeBasis (energyBasis hH) H =
      hamiltonian (fun i => hH.eigenvalues 0+energyGap hH*referenceEnergy i) := by
  rw [hamiltonian_coordinates]
  exact congrArg hamiltonian (energy_affine hH.eigenvalues)

/-- Every spread chain used in `hierarchy` is a complete physical Krylov chain,
with a certified actual commutator recurrence and exact Hilbert--Schmidt Gram
matrix, including the stationary endpoint. -/
theorem spread_chain_certificate {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    PaddedLanczos H hρ.sqrt (spreadChain hH hρ)
      (if energyGap hH=0 then 0 else spreadCoefficient (coordinateDensity hH ρ)
        (coordinateDensity_posSemidef hH hρ)) 1 (energyGap hH) := by
  exact physical_certificate (energyBasis hH) H referenceEnergy (hH.eigenvalues 0)
    (energyGap hH) _ 1 (energyBasis_unitary hH) (energyBasis_unitary_reverse hH)
    (qubit_hamiltonian_affine hH) hρ.sqrt (coordinateDensity_posSemidef hH hρ).sqrt
    (sqrt_coordinates _ hρ (energyBasis_unitary_reverse hH))
    (spread_weights (coordinateDensity_posSemidef hH hρ) (coordinateDensity_trace hH htr))

/-- Every mixed-density chain in the universal inequality is certified in the
original physical basis. -/
theorem mixed_chain_certificate {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    PaddedLanczos H ρ (mixedChain hH ρ)
      (if energyGap hH=0 then 0 else mixedCoefficient (coordinateDensity hH ρ))
      (purity (coordinateDensity hH ρ)) (energyGap hH) := by
  exact physical_certificate (energyBasis hH) H referenceEnergy (hH.eigenvalues 0)
    (energyGap hH) _ _ (energyBasis_unitary hH) (energyBasis_unitary_reverse hH)
    (qubit_hamiltonian_affine hH) ρ (coordinateDensity hH ρ) rfl
    (mixed_weights (coordinateDensity_posSemidef hH hρ) (coordinateDensity_trace hH htr))

/-- Certification for the original rank-one canonical I-purified density and
its actual lifted generator H⊗I. -/
theorem purified_chain_certificate {H ρ : QubitMatrix} (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    PaddedLanczos (PurifiedCovariance.lift H) (Purification.pureSeed hρ.sqrt)
      (purifiedChain hH hρ)
      (if energyGap hH=0 then 0 else purifiedCoefficient (coordinateDensity hH ρ))
      1 (energyGap hH) := by
  apply physical_certificate (PurifiedCovariance.lift (energyBasis hH))
    (PurifiedCovariance.lift H) (fun i : Fin 2 × Fin 2 => referenceEnergy i.1)
    (hH.eigenvalues 0) (energyGap hH) _ 1
    (PurifiedCovariance.lift_unitary _ (energyBasis_unitary hH))
    (PurifiedCovariance.lift_unitary_reverse _ (energyBasis_unitary_reverse hH))
  · rw [PurifiedCovariance.lift_changeBasis, qubit_hamiltonian_affine,
      PurifiedCovariance.lift_diagonal]
  · exact PurifiedCovariance.pureSeed_changeBasis _ _
  · exact purified_weights (coordinateDensity_posSemidef hH hρ) (coordinateDensity_trace hH htr)
      (physical_root_row_weights (energyBasis hH) hρ)

/-- In dimension one every operator seed is stationary under every matrix
Hamiltonian; thus there is no smaller-dimensional hierarchy violation. -/
theorem one_dimensional_commutator (H A : Operator (Fin 1)) : matrixCommutator H A = 0 := by
  ext i j
  fin_cases i; fin_cases j
  simp [matrixCommutator_apply, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]

theorem one_dimensional_chain_certificate (H A : Operator (Fin 1)) (s : ℝ)
    (hs : 0<s) (hn : hsInner A A=(s : ℂ)) :
    PaddedLanczos H A (stationaryChain A) 0 s 0 :=
  stationary_certificate H A s hs hn (one_dimensional_commutator H A)

namespace PaddedLanczos
variable {H A : Operator ι} {v : Fin 3 → Operator ι} {μ s b : ℝ}

/-- The full interior chain has the normalized orthonormal vectors used in
Krylov probabilities. -/
theorem normalized_orthonormal (h : PaddedLanczos H A v μ s b) (hm : 0<μ)
    (k l : Fin 3) : hsInner (normalized (v k)) (normalized (v l)) = if k=l then 1 else 0 := by
  by_cases he : k=l
  · subst l
    simp only [↓reduceIte]
    apply normalized_unit
    rw [h.gram]
    simp only [↓reduceIte, Complex.ofReal_re]
    have hs := h.scale_pos
    have h1 : 0<1-μ := sub_pos.mpr h.mass_lt
    fin_cases k <;> simp [ThreeAtomOperator.norms] <;> positivity
  · simp [normalized, hsInner_smul, h.gram, he]

/-- At the stationary endpoint the surviving seed is a normalized unit
vector and the other displayed vectors are exactly zero. -/
theorem normalized_zero_mass (h : PaddedLanczos H A v 0 s b) :
    hsInner (normalized (v 0)) (normalized (v 0)) = 1 ∧
      normalized (v 1)=0 ∧ normalized (v 2)=0 := by
  obtain ⟨h1,h2⟩ := h.zero_mass_padding
  refine ⟨?_, by simp [h1, normalized], by simp [h2, normalized]⟩
  apply normalized_unit
  rw [h.seed, h.seed_norm]
  exact h.scale_pos

end PaddedLanczos

/-- Explicit all-input completion package: the inequalities and all three
actual ordered-chain certificates, without any hidden nondegeneracy or
full-rank premise. -/
theorem hierarchy_with_certified_chains {H ρ : QubitMatrix}
    (hH : H.IsHermitian) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (t : ℝ) :
    (spread hH hρ t ≤ mixed hH ρ t ∧ mixed hH ρ t ≤ purified hH hρ t) ∧
    PaddedLanczos H hρ.sqrt (spreadChain hH hρ)
      (if energyGap hH=0 then 0 else spreadCoefficient (coordinateDensity hH ρ)
        (coordinateDensity_posSemidef hH hρ)) 1 (energyGap hH) ∧
    PaddedLanczos H ρ (mixedChain hH ρ)
      (if energyGap hH=0 then 0 else mixedCoefficient (coordinateDensity hH ρ))
      (purity (coordinateDensity hH ρ)) (energyGap hH) ∧
    PaddedLanczos (PurifiedCovariance.lift H) (Purification.pureSeed hρ.sqrt)
      (purifiedChain hH hρ)
      (if energyGap hH=0 then 0 else purifiedCoefficient (coordinateDensity hH ρ))
      1 (energyGap hH) :=
  ⟨hierarchy hH hρ htr t, spread_chain_certificate hH hρ htr,
    mixed_chain_certificate hH hρ htr, purified_chain_certificate hH hρ htr⟩

/-- Qubits obey both inequalities, while explicit physical qutrits violate
each side. Dimension-one commutators are zero by the theorem above. -/
theorem qubits_obey_and_qutrits_violate :
    (∀ (H ρ : QubitMatrix) (hH : H.IsHermitian) (hρ : ρ.PosSemidef),
      ρ.trace=1 → ∀ t : ℝ, spread hH hρ t ≤ mixed hH ρ t ∧ mixed hH ρ t ≤ purified hH hρ t) ∧
    chainComplexity States.energyL LeftMixed.seed LeftMixed.chain Real.pi <
      chainComplexity States.energyL LeftSpread.seed LeftSpread.chain Real.pi ∧
    (∑ k : Fin 5, (k.val : ℝ) * matrixProbability PurifiedCovariance.originalGenerator
      PurifiedCovariance.originalSeed (PurifiedCovariance.originalChain k) (Real.pi/3)) <
    (∑ k : Fin 3, (k.val : ℝ) * matrixProbability (States.hR.map Complex.ofReal)
      (States.rhoR.map Complex.ofReal) (rightOriginalChain k) (Real.pi/3)) :=
  ⟨fun _ _ hH hρ htr t => hierarchy hH hρ htr t,
    left_operator_violation, PurifiedCovariance.original_right_violation⟩

end
end Krylov.UniversalQubit
