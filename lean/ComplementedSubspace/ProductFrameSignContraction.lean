import ComplementedSubspace.ProductFrameSignSample

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator
namespace ComplementedSubspace

def frameCoefficientContractedSign (n : ℕ) (p : ℝ)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ)
    (s : SignIndex (Fintype.card (MomentIndex n))) : FrameCoefficient n p :=
  R.mulVec (normalizedFrameSign n s)

private def contractedSignCoefficients (n : ℕ)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (t : FrameIndex n) :
    Fin (Fintype.card (MomentIndex n)) → ℝ := fun j =>
  (Real.sqrt (Fintype.card (MomentIndex n)))⁻¹ *
    (R.transpose.mulVec (realProductFrame n t)) ((Fintype.equivFin (MomentIndex n)).symm j)

private theorem contractedSignCoefficients_length_sq (n : ℕ)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1) (t : FrameIndex n) :
    (∑ j, contractedSignCoefficients n R t j ^ 2) ≤ 1 := by
  unfold contractedSignCoefficients
  simp only [mul_pow, ← Finset.mul_sum]
  rw [(Fintype.equivFin (MomentIndex n)).symm.sum_comp
      (fun i => (R.transpose.mulVec (realProductFrame n t)) i ^ 2),
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    momentIndex_card, Nat.cast_pow, Nat.cast_ofNat]
  have h := sum_sq_mulVec_le R.transpose (realProductFrame n t)
  rw [real_opNorm_transpose, realProductFrame_length_sq] at h
  have hR2 : ‖R‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg R]
  have hsum : (∑ i, R.transpose.mulVec (realProductFrame n t) i ^ 2) ≤ (2 : ℝ) ^ n := by
    calc
      _ ≤ ‖R‖ ^ 2 * (2 : ℝ) ^ n := h
      _ ≤ 1 * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_right hR2 (by positivity)
      _ = _ := one_mul _
  calc
    _ ≤ ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ (by positivity)

private theorem productFrameEval_contractedSign (n : ℕ)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ)
    (s : SignIndex (Fintype.card (MomentIndex n))) (t : FrameIndex n) :
    productFrameEval n (R.mulVec (normalizedFrameSign n s)) t =
      realSignSum (Fintype.card (MomentIndex n)) (contractedSignCoefficients n R t) s := by
  rw [realSignSum_eq_dot]
  unfold productFrameEval Matrix.mulVec dotProduct
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Fintype.sum_equiv (Fintype.equivFin (MomentIndex n))
  intro i
  simp only [contractedSignCoefficients, normalizedFrameSign, Equiv.symm_apply_apply,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem contractedSign_evaluation_moment_le (n : ℕ)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1)
    (t : FrameIndex n) {p : ℝ} (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) :
    finiteAverage (fun s => |productFrameEval n (R.mulVec (normalizedFrameSign n s)) t| ^ p) ≤
      (3 : ℝ) ^ ((p - 2) / 2) := by
  simp only [productFrameEval_contractedSign]
  calc
    _ ≤ (3 : ℝ) ^ ((p - 2) / 2) *
        (∑ j, contractedSignCoefficients n R t j ^ 2) ^ (p / 2) :=
      realSignSum_moment_le _ _ p hp₂ hp₄
    _ ≤ (3 : ℝ) ^ ((p - 2) / 2) * 1 ^ (p / 2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (contractedSignCoefficients_length_sq n R hR t) (by linarith)) (by positivity)
    _ = _ := by rw [Real.one_rpow, mul_one]

theorem frameCoefficientContractedSign_norm_moment_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1) :
    finiteAverage (fun s => ‖frameCoefficientContractedSign n p R s‖ ^ p) ≤
      (3 : ℝ) ^ ((p - 2) / 2) := by
  simp only [frameCoefficient_norm_rpow n p (by linarith : 0 < p)]
  rw [finiteAverage_comm]
  calc
    _ ≤ finiteAverage (fun _ : FrameIndex n => (3 : ℝ) ^ ((p - 2) / 2)) :=
      finiteAverage_mono _ _ fun t => contractedSign_evaluation_moment_le n R hR t hp₂ hp₄
    _ = _ := finiteAverage_const _

/-- A finite-sign replacement for the Gaussian contraction estimate. The
bound is uniform over all coefficient Hilbert contractions. -/
theorem frameCoefficientContractedSign_norm_sq_average_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1) :
    finiteAverage (fun s => ‖frameCoefficientContractedSign n p R s‖ ^ 2) ≤
      (3 : ℝ) ^ ((p - 2) / p) := by
  have hp0 : 0 < p := by linarith
  have hnon := finiteAverage_nonneg
    (fun s => ‖frameCoefficientContractedSign n p R s‖ ^ 2) (fun s => sq_nonneg _)
  apply (Real.rpow_le_rpow_iff hnon (by positivity) (by positivity : 0 < p / 2)).mp
  have hj := finiteAverage_rpow_le
    (fun s => ‖frameCoefficientContractedSign n p R s‖ ^ 2) (fun s => sq_nonneg _)
    (p / 2) (by linarith)
  have hnorm (s : SignIndex (Fintype.card (MomentIndex n))) :
      (‖frameCoefficientContractedSign n p R s‖ ^ 2) ^ (p / 2) =
        ‖frameCoefficientContractedSign n p R s‖ ^ p := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    congr 1
    norm_num <;> ring
  simp only [hnorm] at hj
  calc
    _ ≤ finiteAverage (fun s => ‖frameCoefficientContractedSign n p R s‖ ^ p) := hj
    _ ≤ (3 : ℝ) ^ ((p - 2) / 2) :=
      frameCoefficientContractedSign_norm_moment_le n p hp₂ hp₄ R hR
    _ = ((3 : ℝ) ^ ((p - 2) / p)) ^ (p / 2) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      field_simp
      <;> ring

end ComplementedSubspace
