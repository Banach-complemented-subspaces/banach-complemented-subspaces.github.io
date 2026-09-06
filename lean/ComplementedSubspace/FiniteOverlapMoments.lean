import ComplementedSubspace.ProductFrameMoments

noncomputable section
namespace ComplementedSubspace
open Matrix
open scoped Matrix.Norms.L2Operator

theorem finiteAverage_separated_sum_square
    {ι σ τ : Type*} [Fintype ι] [Fintype σ] [Fintype τ]
    (f : ι → σ → ℝ) (g : ι → τ → ℝ) :
    finiteAverage (fun s : σ × τ => (∑ i, f i s.1 * g i s.2) ^ 2) =
      ∑ i, ∑ j, finiteAverage (fun s => f i s * f j s) *
        finiteAverage (fun t => g i t * g j t) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  simp_rw [finiteAverage_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_mul_mul_comm]
  simpa only [mul_comm] using finiteAverage_separated (fun s : σ => f i s * f j s)
    (fun t : τ => g i t * g j t)

/-- The square of the overlap random variable, sampled on two independent
copies of the actual finite frame. The first frame is normalized to unit
Euclidean length by the factor `1 / 2^n`. -/
def frameOverlapEnergy (n : ℕ) {ι : Type*} [Fintype ι]
    (B V : Matrix (MomentIndex n) ι ℝ) (s : FrameIndex n × FrameIndex n) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ i,
    productFrameEval n (fun k => B k i) s.1 ^ 2 *
      productFrameEval n (fun k => V k i) s.2 ^ 2

theorem frameOverlapEnergy_nonneg (n : ℕ) {ι : Type*} [Fintype ι]
    (B V : Matrix (MomentIndex n) ι ℝ) (s : FrameIndex n × FrameIndex n) :
    0 ≤ frameOverlapEnergy n B V s := by
  unfold frameOverlapEnergy
  positivity

theorem frameOverlapEnergy_average (n : ℕ) {ι : Type*} [Fintype ι]
    (B V : Matrix (MomentIndex n) ι ℝ) :
    finiteAverage (frameOverlapEnergy n B V) =
      ((2 : ℝ) ^ n)⁻¹ * ∑ i, (∑ k, B k i ^ 2) * (∑ k, V k i ^ 2) := by
  unfold frameOverlapEnergy
  rw [finiteAverage_mul, finiteAverage_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteAverage_separated
    (fun s : FrameIndex n => productFrameEval n (fun k => B k i) s ^ 2)
    (fun t : FrameIndex n => productFrameEval n (fun k => V k i) t ^ 2),
    productFrameEval_second_moment, productFrameEval_second_moment]

/-- Exact squared-energy identity before the Hilbert operator norm estimate. -/
theorem frameOverlapEnergy_square_average (n : ℕ) {ι : Type*} [Fintype ι]
    (B V : Matrix (MomentIndex n) ι ℝ) :
    finiteAverage (fun s => frameOverlapEnergy n B V s ^ 2) =
      ∑ i, ∑ j,
        hsInner (rankOne (fun k => B k i)) (tensorMoment n (rankOne (fun k => B k j))) *
        hsInner (rankOne (fun k => V k i)) (tensorMoment n (rankOne (fun k => V k j))) := by
  simp only [frameOverlapEnergy, mul_pow]
  rw [finiteAverage_mul, finiteAverage_separated_sum_square
    (fun i (s : FrameIndex n) => productFrameEval n (fun k => B k i) s ^ 2)
    (fun i (t : FrameIndex n) => productFrameEval n (fun k => V k i) t ^ 2)]
  simp_rw [productFrameEval_paired_fourth_moment]
  have hid (a b : ℝ) : ((2 : ℝ) ^ n * a) * ((2 : ℝ) ^ n * b) =
      ((2 : ℝ) ^ n) ^ 2 * (a * b) := by ring
  simp_rw [hid]
  simp only [← Finset.mul_sum]
  have hn : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- The manuscript's fourth-moment bound, now for concrete finite samples.
The tensor-moment hypothesis is discharged by the verified real induction. -/
theorem frameOverlapEnergy_square_average_le (n : ℕ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B V : Matrix (MomentIndex n) ι ℝ) :
    finiteAverage (fun s => frameOverlapEnergy n B V s ^ 2) ≤
      (Fintype.card ι : ℝ) * (‖B‖ * ‖V‖) ^ 4 * (5 / 8 : ℝ) ^ n := by
  rw [frameOverlapEnergy_square_average]
  exact tensor_paired_column_moments_bound n B V

end ComplementedSubspace
