import ComplementedSubspace.FiniteOverlapLp
import ComplementedSubspace.ProductFrameTraceBound

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ComplementedSubspace

def frameCoefficientRandomized (n : ℕ) (p : ℝ) {m : ℕ}
    (B V : Matrix (MomentIndex n) (Fin m) ℝ) (x : FrameIndex n) (s : SignIndex m) :
    FrameCoefficient n p := fun k =>
  (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * ∑ i,
    realSignVector m s i * productFrameEval n (fun j => V j i) x * B k i

private def overlapSignCoefficients (n : ℕ) {m : ℕ}
    (B V : Matrix (MomentIndex n) (Fin m) ℝ) (x t : FrameIndex n) : Fin m → ℝ := fun i =>
  (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * productFrameEval n (fun j => V j i) x *
    productFrameEval n (fun j => B j i) t

private theorem overlapSignCoefficients_length_sq (n : ℕ) {m : ℕ}
    (B V : Matrix (MomentIndex n) (Fin m) ℝ) (x t : FrameIndex n) :
    (∑ i, overlapSignCoefficients n B V x t i ^ 2) = frameOverlapEnergy n B V (t, x) := by
  simp only [overlapSignCoefficients, mul_pow, inv_pow,
    Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ) ^ n), frameOverlapEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem productFrameEval_randomized (n : ℕ) (p : ℝ) {m : ℕ}
    (B V : Matrix (MomentIndex n) (Fin m) ℝ) (x t : FrameIndex n) (s : SignIndex m) :
    productFrameEval n (frameCoefficientRandomized n p B V x s) t =
      realSignSum m (overlapSignCoefficients n B V x t) s := by
  rw [realSignSum_eq_dot]
  simp only [productFrameEval, frameCoefficientRandomized, Finset.sum_mul,
    Finset.mul_sum, overlapSignCoefficients]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem frameCoefficientRandomized_norm_moment_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) {m : ℕ}
    (B V : Matrix (MomentIndex n) (Fin m) ℝ) :
    finiteAverage (fun x => finiteAverage (fun s => ‖frameCoefficientRandomized n p B V x s‖ ^ p)) ≤
      (3 : ℝ) ^ ((p - 2) / 2) *
        finiteAverage (fun tx => (frameOverlapEnergy n B V tx) ^ (p / 2)) := by
  have hp : 0 < p := by linarith
  simp only [frameCoefficient_norm_rpow n p hp]
  have hpoint (x t : FrameIndex n) :
      finiteAverage (fun s => |productFrameEval n (frameCoefficientRandomized n p B V x s) t| ^ p) ≤
        (3 : ℝ) ^ ((p - 2) / 2) * (frameOverlapEnergy n B V (t, x)) ^ (p / 2) := by
    simp only [productFrameEval_randomized]
    have h := realSignSum_moment_le m (overlapSignCoefficients n B V x t) p hp₂ hp₄
    simpa only [overlapSignCoefficients_length_sq] using h
  calc
    _ = finiteAverage (fun x => finiteAverage (fun t => finiteAverage
        (fun s => |productFrameEval n (frameCoefficientRandomized n p B V x s) t| ^ p))) := by
      congr 1
      funext x
      exact finiteAverage_comm _
    _ ≤ finiteAverage (fun x => finiteAverage (fun t =>
        (3 : ℝ) ^ ((p - 2) / 2) * frameOverlapEnergy n B V (t, x) ^ (p / 2))) :=
      finiteAverage_mono _ _ fun x => finiteAverage_mono _ _ fun t => hpoint x t
    _ = _ := by
      simp only [finiteAverage_mul]
      rw [finiteAverage_comm]
      rw [finiteAverage_prod (fun tx : FrameIndex n × FrameIndex n =>
        frameOverlapEnergy n B V tx ^ (p / 2))]

theorem finiteAverage_le_moment_root {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (p : ℝ) (hp : 1 ≤ p) :
    finiteAverage f ≤ (finiteAverage (fun i => (f i) ^ p)) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hn : 0 ≤ finiteAverage (fun i => (f i) ^ p) :=
    finiteAverage_nonneg _ fun i => Real.rpow_nonneg (hf i) _
  apply (Real.rpow_le_rpow_iff (finiteAverage_nonneg f hf) (Real.rpow_nonneg hn _) hp0).mp
  rw [← Real.rpow_mul hn, one_div_mul_cancel hp0.ne', Real.rpow_one]
  exact finiteAverage_rpow_le f hf p hp

/-- The coefficient component in the unconditional randomization estimate,
with actual finite samples and the exact finite-sign constant. -/
theorem frameCoefficientRandomized_mean_norm_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) {m : ℕ}
    (B V : Matrix (MomentIndex n) (Fin m) ℝ) :
    finiteAverage (fun x => finiteAverage (fun s => ‖frameCoefficientRandomized n p B V x s‖)) ≤
      realFrameSignConstant p *
        (finiteAverage (fun tx => (frameOverlapEnergy n B V tx) ^ (p / 2))) ^ (1 / p) := by
  have hp : 0 < p := by linarith
  have hroot := finiteAverage_le_moment_root
    (fun xs : FrameIndex n × SignIndex m => ‖frameCoefficientRandomized n p B V xs.1 xs.2‖)
    (fun _ => norm_nonneg _) p (by linarith)
  rw [finiteAverage_prod, finiteAverage_prod] at hroot
  have hn : 0 ≤ finiteAverage (fun x => finiteAverage
      (fun s => ‖frameCoefficientRandomized n p B V x s‖ ^ p)) :=
    finiteAverage_nonneg _ fun _ => finiteAverage_nonneg _ fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have he : 0 ≤ finiteAverage (fun tx => frameOverlapEnergy n B V tx ^ (p / 2)) :=
    finiteAverage_nonneg _ fun tx => Real.rpow_nonneg (frameOverlapEnergy_nonneg n B V tx) _
  calc
    _ ≤ (finiteAverage (fun x => finiteAverage
        (fun s => ‖frameCoefficientRandomized n p B V x s‖ ^ p))) ^ (1 / p) := hroot
    _ ≤ ((3 : ℝ) ^ ((p - 2) / 2) *
        finiteAverage (fun tx => frameOverlapEnergy n B V tx ^ (p / 2))) ^ (1 / p) :=
      Real.rpow_le_rpow hn (frameCoefficientRandomized_norm_moment_le n p hp₂ hp₄ B V) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ (3 : ℝ) ^ ((p - 2) / 2)) he,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      unfold realFrameSignConstant
      congr 1
      field_simp
      <;> ring

end ComplementedSubspace
