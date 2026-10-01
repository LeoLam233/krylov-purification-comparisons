import Krylov.Spectral

/-!
This file supplies actual trigonometric time phases to the finite spectral
certificates. Thus the phases are not externally assumed rational data. The
remaining physical bridge is the identification of the original matrix Krylov
chain with its spectral measure.
-/
namespace Krylov.Spectral
open scoped BigOperators
noncomputable section

def realDot {n : ℕ} (w p : Fin n → ℚ) (f : Fin n → ℝ) : ℝ :=
  ∑ i, (w i : ℝ) * (p i : ℝ) * f i

def timeProbability {n : ℕ} (x w p : Fin n → ℚ) (t : ℝ) : ℝ :=
  ((realDot w p (fun i => Real.cos ((x i : ℝ) * t)))^2 +
   (realDot w p (fun i => Real.sin ((x i : ℝ) * t)))^2) / (dot w p p : ℝ)

def timeComplexity {n m : ℕ} (x w : Fin n → ℚ) (p : Fin m → Fin n → ℚ)
    (t : ℝ) : ℝ := ∑ k, (k.val : ℝ) * timeProbability x w (p k) t

/-- The spectral-formula amplitude before normalization, using the actual
complex exponential, not a table of phases. -/
def spectralAmplitude {n : ℕ} (x w p : Fin n → ℚ) (t : ℝ) : ℂ :=
  ∑ i, ((w i : ℝ) * (p i : ℝ) : ℂ) *
    Complex.exp (((-((x i : ℝ) * t) : ℝ) : ℂ) * Complex.I)

theorem amplitude_re {n : ℕ} (x w p : Fin n → ℚ) (t : ℝ) :
    (spectralAmplitude x w p t).re =
      realDot w p (fun i => Real.cos ((x i : ℝ) * t)) := by
  simp [spectralAmplitude, realDot, Complex.mul_re,
    Complex.exp_re]

theorem amplitude_im {n : ℕ} (x w p : Fin n → ℚ) (t : ℝ) :
    (spectralAmplitude x w p t).im =
      -realDot w p (fun i => Real.sin ((x i : ℝ) * t)) := by
  simp [spectralAmplitude, realDot, Complex.mul_im,
    Complex.exp_im, Finset.sum_neg_distrib]

/-- Exact identification of the trigonometric probability with the squared
complex-exponential spectral amplitude divided by the polynomial norm. -/
theorem timeProbability_eq_exp_norm {n : ℕ} (x w p : Fin n → ℚ) (t : ℝ) :
    timeProbability x w p t =
      Complex.normSq (spectralAmplitude x w p t) / (dot w p p : ℝ) := by
  rw [Complex.normSq_apply, amplitude_re, amplitude_im]
  unfold timeProbability
  ring

theorem realDot_cast {n : ℕ} (w p f : Fin n → ℚ) :
    realDot w p (fun i => (f i : ℝ)) = (dot w p f : ℝ) := by
  simp [realDot, dot]

theorem realDot_mul {n : ℕ} (w p : Fin n → ℚ) (f : Fin n → ℝ) (a : ℝ) :
    realDot w p (fun i => a * f i) = a * realDot w p f := by
  simp only [realDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem probability_of_phases {n : ℕ} (x w p c s : Fin n → ℚ) (q : ℚ)
    (a t : ℝ) (ha : a^2 = (q : ℝ))
    (hc : ∀ i, Real.cos ((x i : ℝ)*t) = (c i : ℝ))
    (hs : ∀ i, Real.sin ((x i : ℝ)*t) = a * (s i : ℝ)) :
    timeProbability x w p t = (probability w p c s q : ℝ) := by
  unfold timeProbability
  simp_rw [hc, hs]
  rw [realDot_mul, realDot_cast, realDot_cast, mul_pow, ha]
  norm_cast

theorem right_cos_two : Real.cos (2 * (Real.pi / 3)) = -1/2 := by
  rw [Real.cos_two_mul, Real.cos_pi_div_three]; norm_num

theorem right_sin_two : Real.sin (2 * (Real.pi / 3)) = Real.sqrt 3 / 2 := by
  rw [Real.sin_two_mul, Real.sin_pi_div_three, Real.cos_pi_div_three]; ring

namespace RightMixed

theorem cos_phases : ∀ i,
    Real.cos ((nodes i : ℝ) * (Real.pi/3)) = (cosines i : ℝ) := by
  intro i; fin_cases i <;> norm_num [nodes, cosines, right_cos_two, Real.cos_neg,
    show (-2 : ℝ) * (Real.pi/3) = -(2*(Real.pi/3)) by ring]

theorem sin_phases : ∀ i,
    Real.sin ((nodes i : ℝ) * (Real.pi/3)) = Real.sqrt 3 * (sines i : ℝ) := by
  intro i; fin_cases i <;> norm_num [nodes, sines, right_sin_two, Real.sin_neg,
    show (-2 : ℝ) * (Real.pi/3) = -(2*(Real.pi/3)) by ring] <;> ring

theorem time_probabilities : ∀ k, timeProbability nodes weights (polys k) (Real.pi/3) =
    (probabilities k : ℝ) := by
  intro k
  rw [probability_of_phases nodes weights (polys k) cosines sines 3 (Real.sqrt 3)
    (Real.pi/3) (by norm_num) cos_phases sin_phases, exact_probabilities]

theorem time_complexity : timeComplexity nodes weights polys (Real.pi/3) = 1141425/913952 := by
  simp only [timeComplexity, time_probabilities]
  norm_num [probabilities, Fin.sum_univ_succ]
end RightMixed

namespace RightPurified

theorem cos_phases : ∀ i,
    Real.cos ((nodes i : ℝ) * (Real.pi/3)) = (cosines i : ℝ) := by
  intro i; fin_cases i <;> norm_num [nodes, cosines, right_cos_two, Real.cos_neg,
    Real.cos_pi_div_three,
    show (-2 : ℝ) * (Real.pi/3) = -(2*(Real.pi/3)) by ring]

theorem sin_phases : ∀ i,
    Real.sin ((nodes i : ℝ) * (Real.pi/3)) = Real.sqrt 3 * (sines i : ℝ) := by
  intro i; fin_cases i <;> norm_num [nodes, sines, right_sin_two, Real.sin_neg,
    Real.sin_pi_div_three,
    show (-2 : ℝ) * (Real.pi/3) = -(2*(Real.pi/3)) by ring] <;> ring

theorem time_probabilities : ∀ k, timeProbability nodes weights (polys k) (Real.pi/3) =
    (probabilities k : ℝ) := by
  intro k
  rw [probability_of_phases nodes weights (polys k) cosines sines 3 (Real.sqrt 3)
    (Real.pi/3) (by norm_num) cos_phases sin_phases, exact_probabilities]

theorem time_complexity : timeComplexity nodes weights polys (Real.pi/3) = 2967537/2456246 := by
  simp only [timeComplexity, time_probabilities]
  norm_num [probabilities, Fin.sum_univ_succ]
end RightPurified

theorem right_time_gap :
    timeComplexity RightMixed.nodes RightMixed.weights RightMixed.polys (Real.pi/3) -
    timeComplexity RightPurified.nodes RightPurified.weights RightPurified.polys (Real.pi/3) =
    1600683/39299936 := by
  rw [RightMixed.time_complexity, RightPurified.time_complexity]; norm_num

theorem right_time_violation :
    timeComplexity RightPurified.nodes RightPurified.weights RightPurified.polys (Real.pi/3) <
    timeComplexity RightMixed.nodes RightMixed.weights RightMixed.polys (Real.pi/3) := by
  rw [RightMixed.time_complexity, RightPurified.time_complexity]; norm_num

namespace LeftSpread
theorem cos_phases : ∀ i,
    Real.cos ((nodes i : ℝ) * Real.pi) = (cosines i : ℝ) := by
  intro i; fin_cases i <;> norm_num [nodes, cosines]
theorem sin_phases : ∀ i,
    Real.sin ((nodes i : ℝ) * Real.pi) = (0 : ℝ) * (sines i : ℝ) := by
  intro i; fin_cases i <;> norm_num [nodes, sines]
theorem time_probabilities : ∀ k, timeProbability nodes weights (polys k) Real.pi =
    (probabilities k : ℝ) := by
  intro k
  rw [probability_of_phases nodes weights (polys k) cosines sines 0 0
    Real.pi (by norm_num) cos_phases sin_phases, exact_probabilities]
theorem time_complexity : timeComplexity nodes weights polys Real.pi = 82/441 := by
  simp only [timeComplexity, time_probabilities]
  norm_num [probabilities, Fin.sum_univ_succ]
end LeftSpread

namespace LeftMixed
theorem cos_phases : ∀ i,
    Real.cos ((nodes i : ℝ) * Real.pi) = (cosines i : ℝ) := by
  intro i; fin_cases i <;> norm_num [nodes, cosines]
theorem sin_phases : ∀ i,
    Real.sin ((nodes i : ℝ) * Real.pi) = (0 : ℝ) * (sines i : ℝ) := by
  intro i; fin_cases i <;> norm_num [nodes, sines]
theorem time_probabilities : ∀ k, timeProbability nodes weights (polys k) Real.pi =
    (probabilities k : ℝ) := by
  intro k
  rw [probability_of_phases nodes weights (polys k) cosines sines 0 0
    Real.pi (by norm_num) cos_phases sin_phases, exact_probabilities]
theorem time_complexity : timeComplexity nodes weights polys Real.pi = 1074/8281 := by
  simp only [timeComplexity, time_probabilities]
  norm_num [probabilities, Fin.sum_univ_succ]
end LeftMixed

theorem left_time_gap :
    timeComplexity LeftSpread.nodes LeftSpread.weights LeftSpread.polys Real.pi -
    timeComplexity LeftMixed.nodes LeftMixed.weights LeftMixed.polys Real.pi =
    4192/74529 := by
  rw [LeftSpread.time_complexity, LeftMixed.time_complexity]; norm_num

theorem left_time_violation :
    timeComplexity LeftMixed.nodes LeftMixed.weights LeftMixed.polys Real.pi <
    timeComplexity LeftSpread.nodes LeftSpread.weights LeftSpread.polys Real.pi := by
  rw [LeftSpread.time_complexity, LeftMixed.time_complexity]; norm_num
end
end Krylov.Spectral
