import Mathlib

/-!
Exact finite spectral certificates. The weights, polynomial values, squared norms,
and phases are inputs; all orthogonality and probability calculations are checked
by Lean's kernel. No assertion identifying an arbitrary matrix Krylov chain with
this representation is assumed here.
-/
namespace Krylov.Spectral
open scoped BigOperators

def dot {n : ℕ} (w p q : Fin n → ℚ) : ℚ := ∑ i, w i * p i * q i

def probability {n : ℕ} (w p c s : Fin n → ℚ) (sinSquare : ℚ) : ℚ :=
  ((dot w p c)^2 + sinSquare * (dot w p s)^2) / dot w p p

def complexity {n m : ℕ} (w : Fin n → ℚ) (p : Fin m → Fin n → ℚ)
    (c s : Fin n → ℚ) (sinSquare : ℚ) : ℚ :=
  ∑ k, (k.val : ℚ) * probability w (p k) c s sinSquare

namespace RightMixed

def nodes : Fin 3 → ℚ := ![-2,0,2]
def weights : Fin 3 → ℚ := ![225/1352,451/676,225/1352]
def polys : Fin 3 → Fin 3 → ℚ :=
  ![fun _ => 1, nodes, fun i => nodes i ^ 2 - 225/169]
def norms : Fin 3 → ℚ := ![1,225/169,101475/28561]
def cosines : Fin 3 → ℚ := ![-1/2,1,-1/2]
-- sin(node*pi/3) = sqrt(3) * sines i.
def sines : Fin 3 → ℚ := ![-1/2,0,1/2]
def probabilities : Fin 3 → ℚ := ![458329/1827904,675/2704,913275/1827904]

theorem positive_weights : ∀ i, 0 < weights i := by
  intro i; fin_cases i <;> norm_num [weights]
theorem normalized : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_succ]
theorem gram : ∀ i j, dot weights (polys i) (polys j) =
    if i = j then norms i else 0 := by
  intro i j; fin_cases i <;> fin_cases j <;>
    norm_num [dot, polys, nodes, weights, norms, Fin.sum_univ_succ]
theorem positive_norms : ∀ i, 0 < norms i := by
  intro i; fin_cases i <;> norm_num [norms]
theorem exact_probabilities : ∀ k,
    probability weights (polys k) cosines sines 3 = probabilities k := by
  intro k; fin_cases k <;>
    norm_num [probability, dot, polys, nodes, weights, cosines, sines,
      probabilities, Fin.sum_univ_succ]
theorem sum_probabilities : ∑ k, probabilities k = 1 := by
  norm_num [probabilities, Fin.sum_univ_succ]
theorem exact_complexity : complexity weights polys cosines sines 3 = 1141425/913952 := by
  simp only [complexity, exact_probabilities]
  norm_num [probabilities, Fin.sum_univ_succ]
theorem terminal : ∀ i, nodes i * (nodes i - 2) * (nodes i + 2) = 0 := by
  intro i; fin_cases i <;> norm_num [nodes]
end RightMixed

namespace RightPurified

def nodes : Fin 5 → ℚ := ![-2,-1,0,1,2]
def weights : Fin 5 → ℚ := ![289/2704,153/676,451/1352,153/676,289/2704]
def polys : Fin 5 → Fin 5 → ℚ :=
  ![fun _ => 1, nodes,
    fun i => nodes i ^ 2 - 17/13,
    fun i => nodes i ^ 3 - 77/26 * nodes i,
    fun i => nodes i ^ 4 - 60944/14534 * nodes i ^ 2 + 23409/14534]
def norms : Fin 5 → ℚ := ![1,17/13,731/338,23409/8788,10557459/4912492]
def cosines : Fin 5 → ℚ := ![-1/2,1/2,1,1/2,-1/2]
def sines : Fin 5 → ℚ := ![-1/2,-1/2,0,1/2,1/2]
def probabilities : Fin 5 → ℚ :=
  ![1500625/7311616,62475/140608,45778977/157199744,7803/140608,1173051/314399488]

theorem positive_weights : ∀ i, 0 < weights i := by
  intro i; fin_cases i <;> norm_num [weights]
theorem normalized : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_succ]
theorem gram : ∀ i j, dot weights (polys i) (polys j) =
    if i = j then norms i else 0 := by
  intro i j; fin_cases i <;> fin_cases j <;>
    norm_num [dot, polys, nodes, weights, norms, Fin.sum_univ_succ]
theorem positive_norms : ∀ i, 0 < norms i := by
  intro i; fin_cases i <;> norm_num [norms]
theorem exact_probabilities : ∀ k,
    probability weights (polys k) cosines sines 3 = probabilities k := by
  intro k; fin_cases k <;>
    norm_num [probability, dot, polys, nodes, weights, cosines, sines,
      probabilities, Fin.sum_univ_succ]
theorem sum_probabilities : ∑ k, probabilities k = 1 := by
  norm_num [probabilities, Fin.sum_univ_succ]
theorem exact_complexity : complexity weights polys cosines sines 3 = 2967537/2456246 := by
  simp only [complexity, exact_probabilities]
  norm_num [probabilities, Fin.sum_univ_succ]
theorem terminal : ∀ i,
    nodes i * (nodes i-2) * (nodes i-1) * (nodes i+1) * (nodes i+2) = 0 := by
  intro i; fin_cases i <;> norm_num [nodes]
end RightPurified

theorem right_gap :
    complexity RightMixed.weights RightMixed.polys RightMixed.cosines RightMixed.sines 3 -
    complexity RightPurified.weights RightPurified.polys RightPurified.cosines RightPurified.sines 3 =
    1600683/39299936 := by
  rw [RightMixed.exact_complexity, RightPurified.exact_complexity]; norm_num

theorem right_violation :
    complexity RightPurified.weights RightPurified.polys RightPurified.cosines RightPurified.sines 3 <
    complexity RightMixed.weights RightMixed.polys RightMixed.cosines RightMixed.sines 3 := by
  rw [RightMixed.exact_complexity, RightPurified.exact_complexity]; norm_num


namespace LeftSpread
def nodes : Fin 3 → ℚ := ![-1,0,1]
def weights : Fin 3 → ℚ := ![(1/42)/2,1-(1/42),(1/42)/2]
def polys : Fin 3 → Fin 3 → ℚ :=
  ![fun _ => 1, nodes, fun i => nodes i ^ 2 - (1/42)]
def norms : Fin 3 → ℚ := ![1,(1/42),(1/42)*(1-(1/42))]
def cosines : Fin 3 → ℚ := ![-1,1,-1]
def sines : Fin 3 → ℚ := ![0,0,0]
def probabilities : Fin 3 → ℚ := ![400/441,0,41/441]
theorem positive_weights : ∀ i, 0 < weights i := by
  intro i; fin_cases i <;> norm_num [weights]
theorem normalized : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_succ]
theorem gram : ∀ i j, dot weights (polys i) (polys j) =
    if i = j then norms i else 0 := by
  intro i j; fin_cases i <;> fin_cases j <;>
    norm_num [dot, polys, nodes, weights, norms, Fin.sum_univ_succ]
theorem positive_norms : ∀ i, 0 < norms i := by
  intro i; fin_cases i <;> norm_num [norms]
theorem exact_probabilities : ∀ k,
    probability weights (polys k) cosines sines 0 = probabilities k := by
  intro k; fin_cases k <;>
    norm_num [probability, dot, polys, nodes, weights, cosines, sines,
      probabilities, Fin.sum_univ_succ]
theorem sum_probabilities : ∑ k, probabilities k = 1 := by
  norm_num [probabilities, Fin.sum_univ_succ]
theorem exact_complexity : complexity weights polys cosines sines 0 = 82/441 := by
  simp only [complexity, exact_probabilities]
  norm_num [probabilities, Fin.sum_univ_succ]
theorem terminal : ∀ i, nodes i * (nodes i - 1) * (nodes i + 1) = 0 := by
  intro i; fin_cases i <;> norm_num [nodes]
end LeftSpread

namespace LeftMixed
def nodes : Fin 3 → ℚ := ![-1,0,1]
def weights : Fin 3 → ℚ := ![(3/182)/2,1-(3/182),(3/182)/2]
def polys : Fin 3 → Fin 3 → ℚ :=
  ![fun _ => 1, nodes, fun i => nodes i ^ 2 - (3/182)]
def norms : Fin 3 → ℚ := ![1,(3/182),(3/182)*(1-(3/182))]
def cosines : Fin 3 → ℚ := ![-1,1,-1]
def sines : Fin 3 → ℚ := ![0,0,0]
def probabilities : Fin 3 → ℚ := ![7744/8281,0,537/8281]
theorem positive_weights : ∀ i, 0 < weights i := by
  intro i; fin_cases i <;> norm_num [weights]
theorem normalized : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_succ]
theorem gram : ∀ i j, dot weights (polys i) (polys j) =
    if i = j then norms i else 0 := by
  intro i j; fin_cases i <;> fin_cases j <;>
    norm_num [dot, polys, nodes, weights, norms, Fin.sum_univ_succ]
theorem positive_norms : ∀ i, 0 < norms i := by
  intro i; fin_cases i <;> norm_num [norms]
theorem exact_probabilities : ∀ k,
    probability weights (polys k) cosines sines 0 = probabilities k := by
  intro k; fin_cases k <;>
    norm_num [probability, dot, polys, nodes, weights, cosines, sines,
      probabilities, Fin.sum_univ_succ]
theorem sum_probabilities : ∑ k, probabilities k = 1 := by
  norm_num [probabilities, Fin.sum_univ_succ]
theorem exact_complexity : complexity weights polys cosines sines 0 = 1074/8281 := by
  simp only [complexity, exact_probabilities]
  norm_num [probabilities, Fin.sum_univ_succ]
theorem terminal : ∀ i, nodes i * (nodes i - 1) * (nodes i + 1) = 0 := by
  intro i; fin_cases i <;> norm_num [nodes]
end LeftMixed

theorem left_gap :
    complexity LeftSpread.weights LeftSpread.polys LeftSpread.cosines LeftSpread.sines 0 -
    complexity LeftMixed.weights LeftMixed.polys LeftMixed.cosines LeftMixed.sines 0 =
    4192/74529 := by
  rw [LeftSpread.exact_complexity, LeftMixed.exact_complexity]; norm_num

theorem left_violation :
    complexity LeftMixed.weights LeftMixed.polys LeftMixed.cosines LeftMixed.sines 0 <
    complexity LeftSpread.weights LeftSpread.polys LeftSpread.cosines LeftSpread.sines 0 := by
  rw [LeftSpread.exact_complexity, LeftMixed.exact_complexity]; norm_num

namespace RightMixed
def bSquared : Fin 3 → ℚ := ![0,225/169,451/169]
/-- Exact multiplication-by-energy recurrence, including last-node termination.
This pins the Gram-orthogonal vectors to the ordered Krylov polynomial chain. -/
theorem recurrence : ∀ k i,
    nodes i * polys k i =
      (if h : k.val + 1 < 3 then polys ⟨k.val + 1,h⟩ i else 0) +
      (if h : 0 < k.val then bSquared k * polys ⟨k.val - 1, by omega⟩ i else 0) := by
  intro k i
  fin_cases k <;> fin_cases i <;> norm_num [nodes, polys, bSquared]
end RightMixed

namespace RightPurified
def bSquared : Fin 5 → ℚ := ![0,17/13,43/26,1377/1118,451/559]
/-- Exact multiplication-by-energy recurrence, including last-node termination.
This pins the Gram-orthogonal vectors to the ordered Krylov polynomial chain. -/
theorem recurrence : ∀ k i,
    nodes i * polys k i =
      (if h : k.val + 1 < 5 then polys ⟨k.val + 1,h⟩ i else 0) +
      (if h : 0 < k.val then bSquared k * polys ⟨k.val - 1, by omega⟩ i else 0) := by
  intro k i
  fin_cases k <;> fin_cases i <;> norm_num [nodes, polys, bSquared]
end RightPurified

namespace LeftMixed
def bSquared : Fin 3 → ℚ := ![0,3/182,179/182]
/-- Exact multiplication-by-energy recurrence, including last-node termination.
This pins the Gram-orthogonal vectors to the ordered Krylov polynomial chain. -/
theorem recurrence : ∀ k i,
    nodes i * polys k i =
      (if h : k.val + 1 < 3 then polys ⟨k.val + 1,h⟩ i else 0) +
      (if h : 0 < k.val then bSquared k * polys ⟨k.val - 1, by omega⟩ i else 0) := by
  intro k i
  fin_cases k <;> fin_cases i <;> norm_num [nodes, polys, bSquared]
end LeftMixed

namespace LeftSpread
def bSquared : Fin 3 → ℚ := ![0,1/42,41/42]
/-- Exact multiplication-by-energy recurrence, including last-node termination.
This pins the Gram-orthogonal vectors to the ordered Krylov polynomial chain. -/
theorem recurrence : ∀ k i,
    nodes i * polys k i =
      (if h : k.val + 1 < 3 then polys ⟨k.val + 1,h⟩ i else 0) +
      (if h : 0 < k.val then bSquared k * polys ⟨k.val - 1, by omega⟩ i else 0) := by
  intro k i
  fin_cases k <;> fin_cases i <;> norm_num [nodes, polys, bSquared]
end LeftSpread
end Krylov.Spectral
