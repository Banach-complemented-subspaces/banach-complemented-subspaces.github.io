import ComplementedSubspace.FrameCoefficient
import ComplementedSubspace.ProductFrameLp

/-! # Exact finite-average norm formula for the coefficient space -/

noncomputable section
open scoped BigOperators ENNReal

namespace ComplementedSubspace

theorem frameCoefficient_norm_rpow (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) (b : FrameCoefficient n p) :
    ‖b‖ ^ p = finiteAverage (fun s => |productFrameEval n b s| ^ p) := by
  have h4 : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) n
  have hp' : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hs : 0 ≤ ∑ s, |productFrameEval n b s| ^ p :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  rw [frameCoefficient_norm,
    Real.mul_rpow (frameNormalization_pos n p).le (norm_nonneg _)]
  rw [frameNormalization, ← Real.rpow_mul h4.le]
  have he : (-1 / p) * p = -1 := by field_simp
  rw [he, Real.rpow_neg_one, PiLp.norm_eq_sum (by rwa [hp'])]
  simp only [hp', PiLp.toLp_apply, Real.norm_eq_abs]
  rw [← Real.rpow_mul hs, one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [finiteAverage, frameIndex_card, Nat.cast_pow, Nat.cast_ofNat]

theorem frameCoefficient_norm_eq_average (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) (b : FrameCoefficient n p) :
    ‖b‖ = (finiteAverage (fun s => |productFrameEval n b s| ^ p)) ^ (1 / p) := by
  rw [← frameCoefficient_norm_rpow n p hp b, ← Real.rpow_mul (norm_nonneg b),
    mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The lower Hilbert comparison before taking a pth root. -/
theorem frameCoefficient_hilbert_lower_power (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) (b : FrameCoefficient n p) :
    (∑ i, b i ^ 2) ^ (p / 2) ≤ ‖b‖ ^ p := by
  rw [frameCoefficient_norm_rpow n p (by linarith) b]
  exact productFrameEval_rpow_average_ge n b p hp

/-- The upper comparison uses the uniform H estimate, not the special
single-vector witness norm g. -/
theorem frameCoefficient_hilbert_upper_power (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) (b : FrameCoefficient n p) :
    ‖b‖ ^ p ≤ ((2 : ℝ) ^ n * ∑ i, b i ^ 2) ^ ((p - 2) / 2) * ∑ i, b i ^ 2 := by
  rw [frameCoefficient_norm_rpow n p (by linarith) b]
  exact productFrameEval_rpow_average_le n b p hp

end ComplementedSubspace
