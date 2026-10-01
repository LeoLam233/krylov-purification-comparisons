import Krylov.ComplexAdmissibility

/-! Exact characteristic-polynomial certificates for the manuscript's
proof-internal eigenvalue lists. These record algebraic multiplicities and do
not replace the lists by weaker positivity conclusions. -/
namespace Krylov.FamilyEigenvalues
open Matrix Polynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

lemma two_charpoly (a b c d : ℝ) :
    ( !![a,b;c,d] : Matrix (Fin 2) (Fin 2) ℝ).charpoly =
      (X-C a)*(X-C d)-C b*C c := by
  rw [Matrix.charpoly,Matrix.det_fin_two]
  norm_num [Matrix.charmatrix,Matrix.scalar_apply,Matrix.diagonal,Matrix.map_apply]

lemma symmetric_two_charpoly (a b : ℝ) :
    ( !![a,b;b,a] : Matrix (Fin 2) (Fin 2) ℝ).charpoly =
      (X-C (a+b))*(X-C (a-b)) := by
  rw [two_charpoly]
  simp only [map_add,map_sub]
  ring

lemma three_block_charpoly (a b c : ℝ) :
    ( !![a,0,0;0,b,c;0,c,b] : Matrix (Fin 3) (Fin 3) ℝ).charpoly =
      (X-C a)*(X-C (b+c))*(X-C (b-c)) := by
  let e : Fin 3 ≃ Fin 1 ⊕ Fin 2 := (finSumFinEquiv (m := 1) (n := 2)).symm
  have hh : Matrix.reindex e e ( !![a,0,0;0,b,c;0,c,b] : Matrix (Fin 3) (Fin 3) ℝ) =
      Matrix.fromBlocks ( !![a] : Matrix (Fin 1) (Fin 1) ℝ) 0 0
        ( !![b,c;c,b] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext (i|i) (j|j) <;> fin_cases i <;> fin_cases j <;> rfl
  rw [← Matrix.charpoly_reindex e,hh,Matrix.charpoly_fromBlocks_zero₁₂,symmetric_two_charpoly]
  have h1 : ( !![a] : Matrix (Fin 1) (Fin 1) ℝ).charpoly=X-C a := by
    simp [Matrix.charpoly,Matrix.charmatrix,Matrix.det_unique]
  rw [h1]
  ring

lemma four_block_charpoly (a b c d : ℝ) :
    (TemporalStates.block a b c d).charpoly =
      (X-C (a+b))*(X-C (a-b))*(X-C (c+d))*(X-C (c-d)) := by
  let e : Fin 4 ≃ Fin 2 ⊕ Fin 2 := (finSumFinEquiv (m := 2) (n := 2)).symm
  have hh : Matrix.reindex e e (TemporalStates.block a b c d) =
      Matrix.fromBlocks ( !![a,b;b,a] : Matrix (Fin 2) (Fin 2) ℝ) 0 0
        ( !![c,d;d,c] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext (i|i) (j|j) <;> fin_cases i <;> fin_cases j <;> rfl
  rw [← Matrix.charpoly_reindex e,hh,Matrix.charpoly_fromBlocks_zero₁₂,
    symmetric_two_charpoly,symmetric_two_charpoly]
  ring

lemma diagonal_two_block_charpoly (a b c d : ℝ) :
    ( !![a,0,0,0;0,b,0,0;0,0,c,d;0,0,d,c] : Matrix (Fin 4) (Fin 4) ℝ).charpoly =
      (X-C a)*(X-C b)*(X-C (c+d))*(X-C (c-d)) := by
  let e : Fin 4 ≃ Fin 2 ⊕ Fin 2 := (finSumFinEquiv (m := 2) (n := 2)).symm
  have hh : Matrix.reindex e e
      ( !![a,0,0,0;0,b,0,0;0,0,c,d;0,0,d,c] : Matrix (Fin 4) (Fin 4) ℝ) =
      Matrix.fromBlocks ( !![a,0;0,b] : Matrix (Fin 2) (Fin 2) ℝ) 0 0
        ( !![c,d;d,c] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext (i|i) (j|j) <;> fin_cases i <;> fin_cases j <;> rfl
  rw [← Matrix.charpoly_reindex e,hh,Matrix.charpoly_fromBlocks_zero₁₂,
    two_charpoly,symmetric_two_charpoly]
  simp only [map_zero,mul_zero,sub_zero]
  ring

/-- The exact left witness has the displayed three eigenvalues. -/
theorem left_charpoly : States.rhoL.charpoly =
    (X-C (16/21))*(X-C (4/21))*(X-C (1/21)) := by
  rw [States.rhoL,three_block_charpoly]
  norm_num

/-- The main temporal density has the four eigenvalues printed in its proof. -/
theorem main_charpoly (ε : ℝ) : (TemporalStates.mainState ε).charpoly =
    (X-C (4*(1-ε)/5))*(X-C ((1-ε)/5))*(X-C (4*ε/5))*(X-C (ε/5)) := by
  rw [TemporalStates.mainState,four_block_charpoly]
  congr 2 <;> congr 1 <;> ring

/-- This is the reciprocal family's raw matrix A_η, exactly as in the source. -/
theorem reciprocal_raw_charpoly (η : ℝ) : (TemporalStates.reciprocalRaw η).charpoly =
    (X-C (3*η))*(X-C η)*(X-C (1+η^3))*(X-C (1-η^3)) := by
  rw [TemporalStates.reciprocalRaw,four_block_charpoly]
  congr 2 <;> congr 1 <;> ring

/-- The entire qutrit family has spectrum (m²,4,1)/(m²+5). -/
theorem qutrit_charpoly (m : ℝ) : (FamilyStates.qutritState m).charpoly =
    (X-C (m^2/(m^2+5)))*(X-C (4/(m^2+5)))*(X-C (1/(m^2+5))) := by
  have he : FamilyStates.qutritState m =
      ( !![m^2/(m^2+5),0,0;0,(5/2)/(m^2+5),(3/2)/(m^2+5);
        0,(3/2)/(m^2+5),(5/2)/(m^2+5)] : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [FamilyStates.qutritState,FamilyStates.qutritRaw,FamilyStates.qutritNormalization,
        Matrix.smul_apply,smul_eq_mul] <;> ring
  rw [he,three_block_charpoly]
  congr 2 <;> congr 1 <;> ring

/-- The fixed-purity density's stated four eigenvalues are also certified. -/
theorem fixed_charpoly (ε : ℝ) : (FamilyStates.fixedState ε).charpoly =
    (X-C (Ratios.fixedPurityEigenPlus ε))*(X-C (Ratios.fixedPurityEigenMinus ε))*
      (X-C (4*ε/5))*(X-C (ε/5)) := by
  rw [FamilyStates.fixedState,diagonal_two_block_charpoly]
  congr 2 <;> congr 1 <;> ring

lemma roots_three_linear (a b c : ℝ) :
    ((X-C a)*(X-C b)*(X-C c)).roots=({a} : Multiset ℝ)+{b}+{c} := by
  simp [Polynomial.roots_mul,Polynomial.X_sub_C_ne_zero]

lemma roots_four_linear (a b c d : ℝ) :
    ((X-C a)*(X-C b)*(X-C c)*(X-C d)).roots=({a} : Multiset ℝ)+{b}+{c}+{d} := by
  simp [Polynomial.roots_mul,Polynomial.X_sub_C_ne_zero]

/-- Eigenvalues with algebraic multiplicities, recorded as characteristic roots. -/
theorem left_roots : States.rhoL.charpoly.roots =
    ({16/21} : Multiset ℝ)+{4/21}+{1/21} := by
  rw [left_charpoly,roots_three_linear]

theorem main_roots (ε : ℝ) : (TemporalStates.mainState ε).charpoly.roots =
    ({4*(1-ε)/5} : Multiset ℝ)+{(1-ε)/5}+{4*ε/5}+{ε/5} := by
  rw [main_charpoly,roots_four_linear]

theorem reciprocal_raw_roots (η : ℝ) : (TemporalStates.reciprocalRaw η).charpoly.roots =
    ({3*η} : Multiset ℝ)+{η}+{1+η^3}+{1-η^3} := by
  rw [reciprocal_raw_charpoly,roots_four_linear]

theorem qutrit_roots (m : ℝ) : (FamilyStates.qutritState m).charpoly.roots =
    ({m^2/(m^2+5)} : Multiset ℝ)+{4/(m^2+5)}+{1/(m^2+5)} := by
  rw [qutrit_charpoly,roots_three_linear]

theorem fixed_roots (ε : ℝ) : (FamilyStates.fixedState ε).charpoly.roots =
    ({Ratios.fixedPurityEigenPlus ε} : Multiset ℝ)+{Ratios.fixedPurityEigenMinus ε}+{4*ε/5}+{ε/5} := by
  rw [fixed_charpoly,roots_four_linear]

/-- The same exact polynomial certificates transport to the complex physical
matrices through the standard real-to-complex field embedding. -/
theorem charpoly_complexify {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    (A.map Complex.ofReal).charpoly=A.charpoly.map Complex.ofRealHom :=
  Matrix.charpoly_map A Complex.ofRealHom

end
end Krylov.FamilyEigenvalues
