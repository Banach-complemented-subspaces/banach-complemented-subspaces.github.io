import ComplementedSubspace.FrameCoefficientNorm
import ComplementedSubspace.FiniteParameterBounds

/-!
# The distinguished finite-frame witness and its exact norm

The first product coordinate has Euclidean norm one and coefficient-space
norm exactly `g = alpha_p^n`. Its moment is computed by finite product averages.
This identifies an actual vector in the constructed coefficient space with the
scalar witness scale, while keeping that scale distinct from the uniform bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ENNReal

namespace ComplementedSubspace

/-- The all-first-coordinate index in the recursive binary coefficient space. -/
def firstMomentIndex : (n : ℕ) → MomentIndex n
  | 0 => ()
  | n + 1 => Sum.inl (firstMomentIndex n)

def frameWitness (n : ℕ) : MomentIndex n → ℝ := Pi.single (firstMomentIndex n) 1

/-- The distinguished witness with the actual coefficient norm. -/
def frameCoefficientWitness (n : ℕ) (p : ℝ) : FrameCoefficient n p := frameWitness n

theorem productFrameEval_frameWitness (n : ℕ) (s : FrameIndex n) :
    productFrameEval n (frameWitness n) s = realProductFrame n s (firstMomentIndex n) := by
  classical
  simp [productFrameEval, frameWitness, Pi.single_apply]

theorem frameWitness_euclidean_sq (n : ℕ) : (∑ i, frameWitness n i ^ 2) = 1 := by
  classical
  simp [frameWitness, Pi.single_apply]

theorem realFrame_first_coordinate_moment {p : ℝ} (hp : 0 < p) :
    finiteAverage (fun s : Fin 4 => |realFrame s 0| ^ p) =
      ((2 : ℝ) ^ (p / 2) + 2) / 4 := by
  have hs : Real.sqrt 2 ^ p = (2 : ℝ) ^ (p / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  norm_num [finiteAverage, realFrame, Fin.sum_univ_succ, Real.zero_rpow hp.ne',
    abs_of_nonneg (Real.sqrt_nonneg 2), hs]
  ring

theorem realProductFrame_first_coordinate_moment (n : ℕ) {p : ℝ} (hp : 0 < p) :
    finiteAverage (fun s : FrameIndex n =>
      |realProductFrame n s (firstMomentIndex n)| ^ p) =
        (((2 : ℝ) ^ (p / 2) + 2) / 4) ^ n := by
  induction n with
  | zero =>
    simp only [realProductFrame, abs_one, Real.one_rpow, pow_zero, finiteAverage_const]
  | succ n ih =>
    change finiteAverage (fun s : Fin 4 × FrameIndex n =>
      |realFrame s.1 0 * realProductFrame n s.2 (firstMomentIndex n)| ^ p) = _
    simp only [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    rw [finiteAverage_separated (fun r : Fin 4 => |realFrame r 0| ^ p)
      (fun t : FrameIndex n => |realProductFrame n t (firstMomentIndex n)| ^ p),
      realFrame_first_coordinate_moment hp, ih, pow_succ]
    ring

theorem frameWitness_moment (n : ℕ) {p : ℝ} (hp : 0 < p) :
    finiteAverage (fun s => |productFrameEval n (frameWitness n) s| ^ p) =
      (((2 : ℝ) ^ (p / 2) + 2) / 4) ^ n := by
  simp only [productFrameEval_frameWitness, realProductFrame_first_coordinate_moment n hp]

/-- Exact identification of the constructed witness norm with the scalar `g`. -/
theorem frameCoefficientWitness_norm (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) :
    ‖frameCoefficientWitness n p‖ = realFrameWitnessScale n p := by
  have hg : 0 ≤ realFrameWitnessScale n p := (Real.exp_pos _).le
  apply (Real.rpow_left_inj (norm_nonneg _) hg hp.ne').mp
  rw [frameCoefficient_norm_rpow n p hp, realFrameWitnessScale_rpow n hp.ne']
  exact frameWitness_moment n hp

end ComplementedSubspace
