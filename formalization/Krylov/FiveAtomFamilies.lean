import Krylov.FiveAtom
import Krylov.TemporalStates
import Krylov.ReturnLoss

noncomputable section
namespace Krylov.FiveAtomFamilies
open Matrix OperatorBridge ConcreteChains FiveAtom TemporalStates TemporalFamilies ReturnLoss
open scoped BigOperators

private theorem data_of_real (B : FourLevel) (u v s : ℝ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hz : 0 < FiveAtom.zeroMass u v)
    (hB : ∀ i j, B i j ≠ 0 → energy i-energy j ∈ ({-2,-1,0,1,2} : Finset ℝ))
    (hw : ∀ k, States.operatorGapWeight energy B (FiveAtom.nodes k) / s = FiveAtom.weights u v k) :
    FiveAtom.Data energy (B.map Complex.ofReal) u v s := by
  refine ⟨hs,hu,hv,hz,?_,?_⟩
  · intro i j hn; apply hB i j; simpa using hn
  · intro k
    rw [real_gapWeight]
    have hh := (div_eq_iff hs.ne').mp (hw k)
    linarith

private theorem block_support (a b c d : ℝ) :
    ∀ i j, block a b c d i j ≠ 0 →
      energy i-energy j ∈ ({-2,-1,0,1,2} : Finset ℝ) := by
  intro i j hn
  fin_cases i <;> fin_cases j <;> norm_num [block,energy] at hn ⊢

theorem mainRoot_data {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    FiveAtom.Data energy ((mainRoot ε).map Complex.ofReal) (ε/10) ((1-ε)/10) 1 := by
  have he1 : 0 < 1-ε := by linarith
  apply data_of_real _ _ _ _ (by norm_num) (by positivity) (by positivity)
    (by unfold FiveAtom.zeroMass; linarith)
  · exact block_support _ _ _ _
  · intro k
    have hh := mainRoot_gap_weights he he' k
    change States.operatorGapWeight energy (mainRoot ε) (FiveAtom.nodes k) = _ at hh
    rw [div_one,hh]
    fin_cases k <;> norm_num [FiveAtom.weights,FiveAtom.zeroMass] <;> ring

theorem mainState_data {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) :
    FiveAtom.Data energy ((mainState ε).map Complex.ofReal)
      (9*ε^2/(34*mainD ε)) (9*(1-ε)^2/(34*mainD ε))
      (trace (mainState ε * mainState ε)) := by
  have hd : 0 < mainD ε := by linarith [(mainD_bounds he he').1]
  have he1 : 0 < 1-ε := by linarith
  have hs : 0 < trace (mainState ε * mainState ε) := by
    rw [mainState_purity]; positivity
  apply data_of_real _ _ _ _ hs (by positivity) (by positivity)
    (by have hh := (main_mass_bounds he he').2; unfold FiveAtom.zeroMass; linarith)
  · exact block_support _ _ _ _
  · intro k
    have hh := mainState_gap_weights he he' k
    change States.operatorGapWeight energy (mainState ε) (FiveAtom.nodes k) / _ = _ at hh
    rw [hh]
    fin_cases k <;> norm_num [FiveAtom.weights,FiveAtom.zeroMass] <;>
      field_simp [hd.ne'] <;> unfold mainD <;> ring

theorem reciprocalRoot_data {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    FiveAtom.Data energy ((reciprocalRoot η).map Complex.ofReal)
      (2*(η^2)^3/reciprocalN (η^2)) (2*(η^2)/reciprocalN (η^2)) 1 := by
  have hn := reciprocalN_pos η
  have he2 : 0 < η^2 := sq_pos_of_pos he
  apply data_of_real _ _ _ _ (by norm_num) (by positivity) (by positivity)
    (by have hh := (reciprocal_mass_bounds he2 he').1; unfold FiveAtom.zeroMass; linarith)
  · exact block_support _ _ _ _
  · intro k
    have hh := reciprocalRoot_gap_weights η k
    change States.operatorGapWeight energy (reciprocalRoot η) (FiveAtom.nodes k) = _ at hh
    rw [div_one,hh]
    fin_cases k <;> norm_num [FiveAtom.weights,FiveAtom.zeroMass] <;>
      field_simp [hn.ne'] <;> unfold reciprocalN <;> ring

theorem reciprocalState_data {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) :
    FiveAtom.Data energy ((reciprocalState η).map Complex.ofReal)
      (8*(η^2)^3/reciprocalT (η^2)) (32*(η^2)^2/reciprocalT (η^2))
      (trace (reciprocalState η * reciprocalState η)) := by
  have hn := reciprocalN_pos η
  have ht := reciprocalT_pos η
  have he2 : 0 < η^2 := sq_pos_of_pos he
  have hs : 0 < trace (reciprocalState η * reciprocalState η) := by
    rw [reciprocalState_purity]; positivity
  apply data_of_real _ _ _ _ hs (by positivity) (by positivity)
    (by have hh := (reciprocal_mass_bounds he2 he').2; unfold FiveAtom.zeroMass; linarith)
  · exact block_support _ _ _ _
  · intro k
    have hh := reciprocalState_gap_weights η k
    change States.operatorGapWeight energy (reciprocalState η) (FiveAtom.nodes k) / _ = _ at hh
    rw [hh]
    fin_cases k <;> norm_num [FiveAtom.weights,FiveAtom.zeroMass] <;>
      field_simp [ht.ne'] <;> unfold reciprocalT <;> ring

/-- Physical spread of the main temporal family, from actual operator amplitudes. -/
def mainSpread (ε t : ℝ) : ℝ :=
  let A := (mainRoot ε).map Complex.ofReal
  chainComplexity energy A (FiveAtom.chain energy A (ε/10) ((1-ε)/10)) t

def mainMixed (ε t : ℝ) : ℝ :=
  let A := (mainState ε).map Complex.ofReal
  chainComplexity energy A
    (FiveAtom.chain energy A (9*ε^2/(34*mainD ε)) (9*(1-ε)^2/(34*mainD ε))) t

def reciprocalSpread (η t : ℝ) : ℝ :=
  let A := (reciprocalRoot η).map Complex.ofReal
  chainComplexity energy A (FiveAtom.chain energy A
    (2*(η^2)^3/reciprocalN (η^2)) (2*(η^2)/reciprocalN (η^2))) t

def reciprocalMixed (η t : ℝ) : ℝ :=
  let A := (reciprocalState η).map Complex.ofReal
  chainComplexity energy A (FiveAtom.chain energy A
    (8*(η^2)^3/reciprocalT (η^2)) (32*(η^2)^2/reciprocalT (η^2))) t

theorem continuous_mainSpread (ε : ℝ) : Continuous (mainSpread ε) :=
  FiniteOperator.continuous_chainComplexity _ _ _
theorem continuous_mainMixed (ε : ℝ) : Continuous (mainMixed ε) :=
  FiniteOperator.continuous_chainComplexity _ _ _
theorem continuous_reciprocalSpread (η : ℝ) : Continuous (reciprocalSpread η) :=
  FiniteOperator.continuous_chainComplexity _ _ _
theorem continuous_reciprocalMixed (η : ℝ) : Continuous (reciprocalMixed η) :=
  FiniteOperator.continuous_chainComplexity _ _ _

theorem mainSpread_loss_bounds {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (t : ℝ) :
    mainSpreadLoss ε t ≤ mainSpread ε t ∧ mainSpread ε t ≤ 8*mainSpreadLoss ε t := by
  have he1 : 0 < 1-ε := by linarith
  have ha := five_return_amplitude_bounds (by positivity : 0 ≤ ε/10)
    (by positivity : 0 ≤ (1-ε)/10) (main_mass_bounds he he').1 t
  rw [mainSpreadLoss_eq_return]
  exact FiveAtom.loss_bounds (mainRoot_data he he') t ha.1 ha.2

theorem mainMixed_loss_bounds {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/4) (t : ℝ) :
    mainMixedLoss ε t ≤ mainMixed ε t ∧ mainMixed ε t ≤ 8*mainMixedLoss ε t := by
  have hd : 0 < mainD ε := by linarith [(mainD_bounds he he').1]
  have ha := five_return_amplitude_bounds
    (by positivity : 0 ≤ 9*ε^2/(34*mainD ε))
    (by positivity : 0 ≤ 9*(1-ε)^2/(34*mainD ε)) (main_mass_bounds he he').2 t
  rw [mainMixedLoss_eq_return]
  exact FiveAtom.loss_bounds (mainState_data he he') t ha.1 ha.2

theorem reciprocalSpread_loss_bounds {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) (t : ℝ) :
    reciprocalSpreadLoss (η^2) t ≤ reciprocalSpread η t ∧
      reciprocalSpread η t ≤ 8*reciprocalSpreadLoss (η^2) t := by
  have hn := reciprocalN_pos η
  have ha := five_return_amplitude_bounds
    (by positivity : 0 ≤ 2*(η^2)^3/reciprocalN (η^2))
    (by positivity : 0 ≤ 2*(η^2)/reciprocalN (η^2))
    (reciprocal_mass_bounds (sq_pos_of_pos he) he').1 t
  rw [reciprocalSpreadLoss_eq_return]
  exact FiveAtom.loss_bounds (reciprocalRoot_data he he') t ha.1 ha.2

theorem reciprocalMixed_loss_bounds {η : ℝ} (he : 0 < η) (he' : η^2 ≤ 1/16) (t : ℝ) :
    reciprocalMixedLoss (η^2) t ≤ reciprocalMixed η t ∧
      reciprocalMixed η t ≤ 8*reciprocalMixedLoss (η^2) t := by
  have ht := reciprocalT_pos η
  have ha := five_return_amplitude_bounds
    (by positivity : 0 ≤ 8*(η^2)^3/reciprocalT (η^2))
    (by positivity : 0 ≤ 32*(η^2)^2/reciprocalT (η^2))
    (reciprocal_mass_bounds (sq_pos_of_pos he) he').2 t
  rw [reciprocalMixedLoss_eq_return]
  exact FiveAtom.loss_bounds (reciprocalState_data he he') t ha.1 ha.2

end Krylov.FiveAtomFamilies
