import ComplementedSubspace.ProductFrame
import Mathlib.Analysis.MeanInequalitiesPow

noncomputable section
namespace ComplementedSubspace

theorem finiteAverage_rpow_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (p : ℝ) (hp : 1 ≤ p) :
    (finiteAverage f) ^ p ≤ finiteAverage (fun i => (f i) ^ p) := by
  have hw : (∑ _i : ι, (Fintype.card ι : ℝ)⁻¹) = 1 := by
    simp [Fintype.card_ne_zero]
  have h := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) f (fun _ _ => by positivity) hw
    (fun i _ => hf i) hp
  simpa only [← Finset.mul_sum, finiteAverage] using h

theorem productFrameEval_sq_le (n : ℕ) (b : MomentIndex n → ℝ) (s : FrameIndex n) :
    productFrameEval n b s ^ 2 ≤ (2 : ℝ) ^ n * ∑ i, b i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ b (realProductFrame n s)
  rw [realProductFrame_length_sq] at h
  simpa only [productFrameEval, mul_comm] using h

private theorem abs_rpow_as_square_rpow (x p : ℝ) :
    |x| ^ p = (x ^ 2) ^ (p / 2) := by
  rw [← sq_abs x, ← Real.rpow_natCast_mul (abs_nonneg x)]
  congr 1
  norm_num <;> ring

/-- Lower Hilbert comparison, expressed as a powered norm identity in the
finite averaging convention. -/
theorem productFrameEval_rpow_average_ge (n : ℕ) (b : MomentIndex n → ℝ)
    (p : ℝ) (hp : 2 ≤ p) :
    (∑ i, b i ^ 2) ^ (p / 2) ≤
      finiteAverage (fun s => |productFrameEval n b s| ^ p) := by
  have h := finiteAverage_rpow_le (fun s => productFrameEval n b s ^ 2)
    (fun _ => sq_nonneg _) (p / 2) (by linarith)
  rw [productFrameEval_second_moment] at h
  simpa only [abs_rpow_as_square_rpow] using h

/-- The uniform upper Hilbert comparison needed by the modified overlap proof.
The finite frame is not asserted to be rotationally invariant. -/
theorem productFrameEval_rpow_average_le (n : ℕ) (b : MomentIndex n → ℝ)
    (p : ℝ) (hp : 2 ≤ p) :
    finiteAverage (fun s => |productFrameEval n b s| ^ p) ≤
      ((2 : ℝ) ^ n * ∑ i, b i ^ 2) ^ ((p - 2) / 2) * ∑ i, b i ^ 2 := by
  have hpoint (s : FrameIndex n) : |productFrameEval n b s| ^ p ≤
      ((2 : ℝ) ^ n * ∑ i, b i ^ 2) ^ ((p - 2) / 2) *
        productFrameEval n b s ^ 2 := by
    rw [abs_rpow_as_square_rpow]
    have he : p / 2 = (p - 2) / 2 + 1 := by ring
    rw [he, Real.rpow_add_of_nonneg (sq_nonneg _) (by linarith) zero_le_one,
      Real.rpow_one]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (sq_nonneg _) (productFrameEval_sq_le n b s) (by linarith))
      (sq_nonneg _)
  have h := finiteAverage_mono _ _ hpoint
  rw [finiteAverage_mul, productFrameEval_second_moment] at h
  exact h

end ComplementedSubspace
