import ComplementedSubspace.FrameCoefficientNorm
import ComplementedSubspace.FiniteSignsInterpolation

/-!
# Normalized independent signs in the actual coefficient space

The sample vectors have Euclidean norm one and covariance `I / 2^n`.
Finite sign interpolation and finite Fubini bound their average coefficient
norm squared by `3^((p-2)/p)` for exponents between two and four.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ENNReal

namespace ComplementedSubspace

private theorem signCoordinateCovariance (d : ℕ) (i j : Fin d) :
    finiteAverage (fun s => realSignVector d s i * realSignVector d s j) =
      if i = j then 1 else 0 := by
  classical
  have h := realSignSum_covariance d (Pi.single i 1) (Pi.single j 1)
  simpa [realSignSum_eq_dot, Pi.single_apply, eq_comm] using h

/-- Independent signs reindexed onto the binary coefficient coordinates and
normalized to Euclidean norm one. -/
def normalizedFrameSign (n : ℕ)
    (s : SignIndex (Fintype.card (MomentIndex n))) (i : MomentIndex n) : ℝ :=
  (Real.sqrt (Fintype.card (MomentIndex n)))⁻¹ *
    realSignVector (Fintype.card (MomentIndex n)) s (Fintype.equivFin (MomentIndex n) i)

/-- The same vector with the actual coefficient-space norm. -/
def frameCoefficientSignSample (n : ℕ) (p : ℝ)
    (s : SignIndex (Fintype.card (MomentIndex n))) : FrameCoefficient n p :=
  normalizedFrameSign n s

theorem normalizedFrameSign_length_sq (n : ℕ)
    (s : SignIndex (Fintype.card (MomentIndex n))) :
    (∑ i, normalizedFrameSign n s i ^ 2) = 1 := by
  unfold normalizedFrameSign
  rw [(Fintype.equivFin (MomentIndex n)).sum_comp (fun j =>
    ((Real.sqrt (Fintype.card (MomentIndex n)))⁻¹ *
      realSignVector (Fintype.card (MomentIndex n)) s j) ^ 2)]
  exact normalizedRealSignVector_length_sq _ (by rw [momentIndex_card]; positivity) s

theorem normalizedFrameSign_covariance (n : ℕ) (i j : MomentIndex n) :
    finiteAverage (fun s => normalizedFrameSign n s i * normalizedFrameSign n s j) =
      (if i = j then 1 else 0) / (2 : ℝ) ^ n := by
  unfold normalizedFrameSign
  simp_rw [mul_mul_mul_comm]
  rw [finiteAverage_mul, signCoordinateCovariance]
  rw [← pow_two, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [Equiv.apply_eq_iff_eq, momentIndex_card, Nat.cast_pow, Nat.cast_ofNat]
  ring

private def frameSignCoefficients (n : ℕ) (t : FrameIndex n) :
    Fin (Fintype.card (MomentIndex n)) → ℝ := fun j =>
  (Real.sqrt (Fintype.card (MomentIndex n)))⁻¹ *
    realProductFrame n t ((Fintype.equivFin (MomentIndex n)).symm j)

private theorem frameSignCoefficients_length_sq (n : ℕ) (t : FrameIndex n) :
    (∑ j, frameSignCoefficients n t j ^ 2) = 1 := by
  unfold frameSignCoefficients
  simp only [mul_pow, ← Finset.mul_sum]
  rw [(Fintype.equivFin (MomentIndex n)).symm.sum_comp
      (fun i => realProductFrame n t i ^ 2),
    realProductFrame_length_sq, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    momentIndex_card, Nat.cast_pow, Nat.cast_ofNat]
  exact inv_mul_cancel₀ (by positivity)

private theorem productFrameEval_normalizedFrameSign (n : ℕ)
    (s : SignIndex (Fintype.card (MomentIndex n))) (t : FrameIndex n) :
    productFrameEval n (normalizedFrameSign n s) t =
      realSignSum (Fintype.card (MomentIndex n)) (frameSignCoefficients n t) s := by
  rw [realSignSum_eq_dot]
  unfold productFrameEval
  apply Fintype.sum_equiv (Fintype.equivFin (MomentIndex n))
  intro i
  simp only [normalizedFrameSign, frameSignCoefficients, Equiv.symm_apply_apply]
  ring

theorem normalizedFrameSign_evaluation_moment_le (n : ℕ) (t : FrameIndex n)
    {p : ℝ} (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) :
    finiteAverage (fun s => |productFrameEval n (normalizedFrameSign n s) t| ^ p) ≤
      (3 : ℝ) ^ ((p - 2) / 2) := by
  simp only [productFrameEval_normalizedFrameSign]
  have h := realSignSum_moment_le _ (frameSignCoefficients n t) p hp₂ hp₄
  simpa only [frameSignCoefficients_length_sq, Real.one_rpow, mul_one] using h

theorem finiteAverage_comm {σ τ : Type*} [Fintype σ] [Fintype τ] (f : σ → τ → ℝ) :
    finiteAverage (fun s => finiteAverage (fun t => f s t)) =
      finiteAverage (fun t => finiteAverage (fun s => f s t)) := by
  change finiteAverage (fun s => (Fintype.card τ : ℝ)⁻¹ * ∑ t, f s t) =
    (Fintype.card τ : ℝ)⁻¹ * ∑ t, finiteAverage (fun s => f s t)
  rw [finiteAverage_mul, finiteAverage_sum]

theorem frameCoefficientSignSample_norm_moment_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) :
    finiteAverage (fun s => ‖frameCoefficientSignSample n p s‖ ^ p) ≤
      (3 : ℝ) ^ ((p - 2) / 2) := by
  simp only [frameCoefficient_norm_rpow n p (by linarith : 0 < p)]
  rw [finiteAverage_comm]
  calc
    _ ≤ finiteAverage (fun _ : FrameIndex n => (3 : ℝ) ^ ((p - 2) / 2)) :=
      finiteAverage_mono _ _ fun t => normalizedFrameSign_evaluation_moment_le n t hp₂ hp₄
    _ = _ := finiteAverage_const _

/-- The coefficient-sign substitute for the Gaussian second-moment bound. -/
theorem frameCoefficientSignSample_norm_sq_average_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) :
    finiteAverage (fun s => ‖frameCoefficientSignSample n p s‖ ^ 2) ≤
      (3 : ℝ) ^ ((p - 2) / p) := by
  have hp0 : 0 < p := by linarith
  have hnon := finiteAverage_nonneg
    (fun s => ‖frameCoefficientSignSample n p s‖ ^ 2) (fun s => sq_nonneg _)
  apply (Real.rpow_le_rpow_iff hnon (by positivity) (by positivity : 0 < p / 2)).mp
  have hj := finiteAverage_rpow_le
    (fun s => ‖frameCoefficientSignSample n p s‖ ^ 2) (fun s => sq_nonneg _)
    (p / 2) (by linarith)
  have hnorm (s : SignIndex (Fintype.card (MomentIndex n))) :
      (‖frameCoefficientSignSample n p s‖ ^ 2) ^ (p / 2) =
        ‖frameCoefficientSignSample n p s‖ ^ p := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    congr 1
    norm_num <;> ring
  simp only [hnorm] at hj
  calc
    _ ≤ finiteAverage (fun s => ‖frameCoefficientSignSample n p s‖ ^ p) := hj
    _ ≤ (3 : ℝ) ^ ((p - 2) / 2) := frameCoefficientSignSample_norm_moment_le n p hp₂ hp₄
    _ = ((3 : ℝ) ^ ((p - 2) / p)) ^ (p / 2) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      field_simp
      <;> ring

end ComplementedSubspace
