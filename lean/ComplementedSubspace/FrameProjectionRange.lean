import ComplementedSubspace.TensorProjection
import ComplementedSubspace.ProductFrame

/-! The checked tensor projector has exactly the product-frame coefficient range. -/

noncomputable section
open scoped BigOperators ENNReal Kronecker
open Matrix WithLp

namespace ComplementedSubspace

lemma realFrameProjection_entry (s t : Fin 4) :
    realFrameProjection s t = (1 / 4 : ℝ) *
      (realFrame s 0 * realFrame t 0 + realFrame s 1 * realFrame t 1) := by
  change (1 / 4 : ℝ) * (∑ j : Fin 2, realFrame s j * realFrame t j) = _
  rw [Fin.sum_univ_two]

set_option backward.isDefEq.respectTransparency false in
theorem tensorFrameProjection_eq_gram (n : ℕ) :
    tensorFrameProjection n = ((4 : ℝ) ^ n)⁻¹ •
      (realProductFrame n * (realProductFrame n).transpose) := by
  induction n with
  | zero =>
    ext s t
    cases s
    cases t
    simp [tensorFrameProjection, realProductFrame, MomentIndex, Matrix.mul_apply]
  | succ n ih =>
    ext s t
    change realFrameProjection s.1 t.1 * tensorFrameProjection n s.2 t.2 = _
    have htail := congrArg (fun M => M s.2 t.2) ih
    rw [htail, realFrameProjection_entry]
    change (1 / 4 : ℝ) *
      (realFrame s.1 0 * realFrame t.1 0 + realFrame s.1 1 * realFrame t.1 1) *
      (((4 : ℝ) ^ n)⁻¹ * ∑ i, realProductFrame n s.2 i * realProductFrame n t.2 i) =
      ((4 : ℝ) ^ (n + 1))⁻¹ * ∑ i : MomentIndex n ⊕ MomentIndex n,
        realProductFrame (n + 1) s i * realProductFrame (n + 1) t i
    rw [Fintype.sum_sum_type]
    simp only [realProductFrame]
    have hfactor (a b : ℝ) :
        (∑ i : MomentIndex n, (a * realProductFrame n s.2 i) *
          (b * realProductFrame n t.2 i)) =
        (a * b) * ∑ i, realProductFrame n s.2 i * realProductFrame n t.2 i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfactor (realFrame s.1 0) (realFrame t.1 0),
      hfactor (realFrame s.1 1) (realFrame t.1 1), pow_succ, _root_.mul_inv_rev]
    ring

theorem realProductFrame_gram (n : ℕ) :
    (realProductFrame n).transpose * realProductFrame n = (4 : ℝ) ^ n • 1 := by
  ext i j
  have h := realProductFrame_covariance n i j
  change (Fintype.card (FrameIndex n) : ℝ)⁻¹ *
    (∑ s, realProductFrame n s i * realProductFrame n s j) =
      (if i = j then 1 else 0) at h
  rw [frameIndex_card, Nat.cast_pow, Nat.cast_ofNat] at h
  have hm := congrArg (fun r : ℝ => (4 : ℝ) ^ n * r) h
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n (by norm_num : (4 : ℝ) ≠ 0)),
    one_mul] at hm
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply] using hm

theorem tensorFrameProjection_mul_frame (n : ℕ) :
    tensorFrameProjection n * realProductFrame n = realProductFrame n := by
  rw [tensorFrameProjection_eq_gram, Matrix.smul_mul, Matrix.mul_assoc,
    realProductFrame_gram, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  simp [pow_ne_zero n (by norm_num : (4 : ℝ) ≠ 0)]

theorem tensorFrameProjection_clm_fixes_frame (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ)
    (b : PiLp p (fun _ : MomentIndex n => ℝ)) :
    matrixPiLpCLM p (tensorFrameProjection n) (matrixPiLpCLM p (realProductFrame n) b) =
      matrixPiLpCLM p (realProductFrame n) b := by
  have h := congrArg (fun F => F b)
    (matrixPiLpCLM_comp p (tensorFrameProjection n) (realProductFrame n))
  rw [tensorFrameProjection_mul_frame] at h
  exact h

theorem tensorFrameProjection_range_eq (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    (matrixPiLpCLM p (tensorFrameProjection n)).range =
      (matrixPiLpCLM p (realProductFrame n)).range := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    refine ⟨toLp p (((4 : ℝ) ^ n)⁻¹ • ((realProductFrame n).transpose *ᵥ ofLp x)), ?_⟩
    ext i
    change (realProductFrame n *ᵥ
      (((4 : ℝ) ^ n)⁻¹ • ((realProductFrame n).transpose *ᵥ ofLp x))) i =
        (tensorFrameProjection n *ᵥ ofLp x) i
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, tensorFrameProjection_eq_gram,
      Matrix.smul_mulVec]
  · intro y hy
    obtain ⟨b, rfl⟩ := hy
    exact ⟨matrixPiLpCLM p (realProductFrame n) b,
      tensorFrameProjection_clm_fixes_frame p n b⟩

theorem matrixPiLpCLM_realProductFrame_injective (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    Function.Injective (matrixPiLpCLM p (realProductFrame n)) := by
  intro b c h
  apply ofLp_injective p
  apply productFrameEval_injective n
  funext s
  have hs := congrArg (fun x => x s) h
  simpa only [matrixPiLpCLM_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
    productFrameEval, mul_comm] using hs

end ComplementedSubspace
