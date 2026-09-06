import ComplementedSubspace.FrameCoefficientNorm
import ComplementedSubspace.FiniteParameterBounds
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # The coefficient Hilbert norm and its exact comparison scale -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal

namespace ComplementedSubspace

/-- The identity on coordinates, between the actual frame norm and Euclidean norm. -/
def frameCoefficientHilbertEquiv (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    FrameCoefficient n p ≃L[ℝ] EuclideanSpace ℝ (MomentIndex n) :=
  (show FrameCoefficient n p ≃ₗ[ℝ] EuclideanSpace ℝ (MomentIndex n) from
    (WithLp.linearEquiv 2 ℝ (MomentIndex n → ℝ)).symm).toContinuousLinearEquiv

@[simp] theorem frameCoefficientHilbertEquiv_apply (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (b : FrameCoefficient n p) (i : MomentIndex n) :
    frameCoefficientHilbertEquiv n p b i = b i := rfl

theorem frameCoefficientHilbertEquiv_norm_sq (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (b : FrameCoefficient n p) :
    ‖frameCoefficientHilbertEquiv n p b‖ ^ 2 = ∑ i, b i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

theorem frameCoefficient_hilbert_lower (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) (b : FrameCoefficient n p) :
    ‖frameCoefficientHilbertEquiv n p b‖ ≤ ‖b‖ := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) (by linarith : 0 < p)).mp
  have h := frameCoefficient_hilbert_lower_power n p hp b
  rw [← frameCoefficientHilbertEquiv_norm_sq] at h
  convert h using 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  norm_num
  ring

theorem frameCoefficient_hilbert_upper (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) (b : FrameCoefficient n p) :
    ‖b‖ ≤ realFrameHilbertScale n p * ‖frameCoefficientHilbertEquiv n p b‖ := by
  have hp0 : 0 < p := by linarith
  let r := ‖frameCoefficientHilbertEquiv n p b‖
  have hr : 0 ≤ r := norm_nonneg _
  have hH : 0 ≤ realFrameHilbertScale n p := (Real.exp_pos _).le
  have h := frameCoefficient_hilbert_upper_power n p hp b
  rw [← frameCoefficientHilbertEquiv_norm_sq] at h
  apply (Real.rpow_le_rpow_iff (norm_nonneg _)
    (mul_nonneg hH hr) hp0).mp
  apply h.trans
  change ((2 : ℝ) ^ n * r ^ 2) ^ ((p - 2) / 2) * r ^ 2 ≤
    (realFrameHilbertScale n p * r) ^ p
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · rw [← hr0]
    simp [Real.zero_rpow hp0.ne']
  · apply le_of_eq
    rw [Real.mul_rpow (by positivity) (sq_nonneg r),
      Real.mul_rpow hH hr,
      realFrameHilbertScale_eq, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have htwo : ((2 : ℝ) ^ n) ^ ((p - 2) / 2) =
        (2 : ℝ) ^ ((n : ℝ) * (1 / 2 - 1 / p) * p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      field_simp
    rw [htwo, mul_assoc]
    congr 1
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr, ← Real.rpow_add hr0]
    congr 1
    norm_num
    ring

theorem frameCoefficientHilbertEquiv_norm_le_one (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) :
    ‖(frameCoefficientHilbertEquiv n p).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro b
  change ‖frameCoefficientHilbertEquiv n p b‖ ≤ 1 * ‖b‖
  simpa only [one_mul] using frameCoefficient_hilbert_lower n p hp b

theorem frameCoefficientHilbertEquiv_symm_norm_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) :
    ‖(frameCoefficientHilbertEquiv n p).symm.toContinuousLinearMap‖ ≤
      realFrameHilbertScale n p := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (show 0 ≤ realFrameHilbertScale n p from (Real.exp_pos _).le)
  intro b
  change ‖(frameCoefficientHilbertEquiv n p).symm b‖ ≤ realFrameHilbertScale n p * ‖b‖
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    frameCoefficient_hilbert_upper n p hp ((frameCoefficientHilbertEquiv n p).symm b)

end ComplementedSubspace
