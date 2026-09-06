import ComplementedSubspace.FiniteOverlapMoments
import ComplementedSubspace.FiniteSignsInterpolation

noncomputable section
open scoped Matrix.Norms.L2Operator
namespace ComplementedSubspace

theorem frameOverlapEnergy_average_le (n : ℕ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B V : Matrix (MomentIndex n) ι ℝ) :
    finiteAverage (frameOverlapEnergy n B V) ≤ (‖B‖ * ‖V‖) ^ 2 := by
  have hB : (∑ i, ∑ k, B k i ^ 2) ≤ (2 : ℝ) ^ n * ‖B‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _k : MomentIndex n, ‖B.transpose‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        exact column_sq_le_opNorm_sq B.transpose k
      _ = _ := by simp [real_opNorm_transpose, momentIndex_card]
  have hsum : (∑ i, (∑ k, B k i ^ 2) * (∑ k, V k i ^ 2)) ≤
      (2 : ℝ) ^ n * (‖B‖ * ‖V‖) ^ 2 := by
    calc
      _ ≤ ∑ i, (∑ k, B k i ^ 2) * ‖V‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (column_sq_le_opNorm_sq V i)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = (∑ i, ∑ k, B k i ^ 2) * ‖V‖ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ ((2 : ℝ) ^ n * ‖B‖ ^ 2) * ‖V‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hB (sq_nonneg _)
      _ = _ := by ring
  rw [frameOverlapEnergy_average]
  have h := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ ((2 : ℝ) ^ n)⁻¹)
  have hn : (2 : ℝ) ^ n ≠ 0 := by positivity
  simpa only [← mul_assoc, inv_mul_cancel₀ hn, one_mul] using h

/-- The complete second-to-fourth interpolation estimate for the concrete
finite-frame overlap random variable. -/
theorem frameOverlapEnergy_rpow_average_le (n : ℕ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B V : Matrix (MomentIndex n) ι ℝ)
    (p : ℝ) (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) :
    finiteAverage (fun s => (Real.sqrt (frameOverlapEnergy n B V s)) ^ p) ≤
      ((Fintype.card ι : ℝ) * (5 / 8 : ℝ) ^ n) ^ ((p - 2) / 2) *
        (‖B‖ * ‖V‖) ^ p := by
  have h₂ : finiteAverage (fun s => Real.sqrt (frameOverlapEnergy n B V s) ^ 2) ≤
      (‖B‖ * ‖V‖) ^ 2 := by
    simp_rw [Real.sq_sqrt (frameOverlapEnergy_nonneg n B V _)]
    exact frameOverlapEnergy_average_le n B V
  have h₄ : finiteAverage (fun s => Real.sqrt (frameOverlapEnergy n B V s) ^ 4) ≤
      ((Fintype.card ι : ℝ) * (5 / 8 : ℝ) ^ n) * ((‖B‖ * ‖V‖) ^ 2) ^ 2 := by
    have hi (s) : Real.sqrt (frameOverlapEnergy n B V s) ^ 4 =
        frameOverlapEnergy n B V s ^ 2 := by
      calc
        _ = (Real.sqrt (frameOverlapEnergy n B V s) ^ 2) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (frameOverlapEnergy_nonneg n B V s)]
    simp_rw [hi]
    convert frameOverlapEnergy_square_average_le n B V using 1 <;> ring
  have h := finiteAverage_moment_bound _ (fun _ => Real.sqrt_nonneg _) p
    ((‖B‖ * ‖V‖) ^ 2) ((Fintype.card ι : ℝ) * (5 / 8 : ℝ) ^ n)
    hp₂ hp₄ (sq_nonneg _) (by positivity) h₂ h₄
  have he : (((‖B‖ * ‖V‖) ^ 2) : ℝ) ^ (p / 2) = (‖B‖ * ‖V‖) ^ p := by
    rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ ‖B‖ * ‖V‖)]
    congr 1
    norm_num <;> ring
  simpa only [he] using h

theorem frameOverlapEnergy_moment_root_le_of_second (n : ℕ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B V : Matrix (MomentIndex n) ι ℝ)
    (p : ℝ) (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) (A : ℝ) (hA : 0 ≤ A)
    (hsecond : finiteAverage (frameOverlapEnergy n B V) ≤ A) :
    (finiteAverage (fun s => frameOverlapEnergy n B V s ^ (p / 2))) ^ (1 / p) ≤
      A ^ ((4 - p) / (2 * p)) *
        ((Fintype.card ι : ℝ) * (‖B‖ * ‖V‖) ^ 4 * (5 / 8 : ℝ) ^ n) ^ ((p - 2) / (2 * p)) := by
  have hp : 0 < p := by linarith
  let f := fun s => Real.sqrt (frameOverlapEnergy n B V s)
  have hsq (s) : f s ^ 2 = frameOverlapEnergy n B V s :=
    Real.sq_sqrt (frameOverlapEnergy_nonneg n B V s)
  have hfour (s) : f s ^ 4 = frameOverlapEnergy n B V s ^ 2 := by
    calc
      _ = (f s ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  have hpow (s) : (frameOverlapEnergy n B V s) ^ (p / 2) = f s ^ p := by
    rw [← hsq, ← Real.rpow_natCast_mul (Real.sqrt_nonneg _)]
    congr 1
    norm_num <;> ring
  have hi := finiteAverage_moment_interpolation f (fun _ => Real.sqrt_nonneg _) p hp₂ hp₄
  simp only [hsq, hfour] at hi
  have hm : finiteAverage (fun s => f s ^ p) ≤
      A ^ ((4 - p) / 2) *
        ((Fintype.card ι : ℝ) * (‖B‖ * ‖V‖) ^ 4 * (5 / 8 : ℝ) ^ n) ^ ((p - 2) / 2) := by
    apply hi.trans
    exact mul_le_mul
      (Real.rpow_le_rpow (finiteAverage_nonneg _ (frameOverlapEnergy_nonneg n B V)) hsecond (by linarith))
      (Real.rpow_le_rpow (finiteAverage_nonneg _ (fun _ => sq_nonneg _))
        (frameOverlapEnergy_square_average_le n B V) (by linarith))
      (Real.rpow_nonneg (finiteAverage_nonneg _ (fun _ => sq_nonneg _)) _)
      (Real.rpow_nonneg hA _)
  simp only [hpow]
  have hroot := Real.rpow_le_rpow
    (finiteAverage_nonneg _ fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _) hm
    (by positivity : 0 ≤ 1 / p)
  apply hroot.trans_eq
  rw [Real.mul_rpow (Real.rpow_nonneg hA _)
      (by positivity : 0 ≤ ((Fintype.card ι : ℝ) * (‖B‖ * ‖V‖) ^ 4 * (5 / 8 : ℝ) ^ n) ^ ((p - 2) / 2)),
    ← Real.rpow_mul hA, ← Real.rpow_mul (by positivity :
      0 ≤ (Fintype.card ι : ℝ) * (‖B‖ * ‖V‖) ^ 4 * (5 / 8 : ℝ) ^ n)]
  congr 1 <;> congr 1 <;> field_simp <;> ring

end ComplementedSubspace
