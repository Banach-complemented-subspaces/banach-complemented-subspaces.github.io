import ComplementedSubspace.ComplexFrameCoefficient
import ComplementedSubspace.ComplexTensorProjection

/-! Exact complex coefficient-space identification with the tensor projection range. -/

noncomputable section
open scoped BigOperators ENNReal
open Matrix WithLp
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

theorem complexTensorFrameProjection_eq_gram (n : ℕ) :
    complexTensorFrameProjection n = (((4 : ℝ) ^ n)⁻¹ : ℂ) •
      (complexifyMatrix (realProductFrame n) *
        (complexifyMatrix (realProductFrame n)).transpose) := by
  rw [complexTensorFrameProjection, tensorFrameProjection_eq_gram]
  have ht : complexifyMatrix (realProductFrame n).transpose =
      (complexifyMatrix (realProductFrame n)).transpose := rfl
  rw [← ht, ← complexifyMatrix_mul]
  ext i j
  simp [complexifyMatrix, Matrix.smul_apply]

theorem complexTensorFrameProjection_mul_frame (n : ℕ) :
    complexTensorFrameProjection n * complexifyMatrix (realProductFrame n) =
      complexifyMatrix (realProductFrame n) := by
  rw [complexTensorFrameProjection, ← complexifyMatrix_mul, tensorFrameProjection_mul_frame]

theorem complexTensorFrameProjection_clm_fixes_frame (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ)
    (b : PiLp p (fun _ : MomentIndex n => ℂ)) :
    complexMatrixPiLpCLM p (complexTensorFrameProjection n)
      (complexMatrixPiLpCLM p (complexifyMatrix (realProductFrame n)) b) =
      complexMatrixPiLpCLM p (complexifyMatrix (realProductFrame n)) b := by
  have h := congrArg (fun F => F b)
    (complexMatrixPiLpCLM_comp p (complexTensorFrameProjection n) (complexifyMatrix (realProductFrame n)))
  rw [complexTensorFrameProjection_mul_frame] at h
  exact h

theorem complexTensorFrameProjection_range_eq (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    (complexMatrixPiLpCLM p (complexTensorFrameProjection n)).range =
      (complexMatrixPiLpCLM p (complexifyMatrix (realProductFrame n))).range := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨toLp p ((((4 : ℝ) ^ n)⁻¹ : ℂ) •
      ((complexifyMatrix (realProductFrame n)).transpose *ᵥ ofLp x)), ?_⟩
    ext i
    change (complexifyMatrix (realProductFrame n) *ᵥ
      ((((4 : ℝ) ^ n)⁻¹ : ℂ) •
        ((complexifyMatrix (realProductFrame n)).transpose *ᵥ ofLp x))) i =
      (complexTensorFrameProjection n *ᵥ ofLp x) i
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, complexTensorFrameProjection_eq_gram,
      Matrix.smul_mulVec]
  · rintro y ⟨b, rfl⟩
    exact ⟨complexMatrixPiLpCLM p (complexifyMatrix (realProductFrame n)) b,
      complexTensorFrameProjection_clm_fixes_frame p n b⟩

theorem complexFrameCoefficientEmbedding_range_eq (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    (complexFrameCoefficientEmbedding n p).range =
      (complexMatrixPiLpCLM (ENNReal.ofReal p) (complexifyMatrix (realProductFrame n))).range := by
  apply le_antisymm
  · rintro y ⟨b, rfl⟩
    refine ⟨(frameNormalization n p : ℂ) • WithLp.toLp (ENNReal.ofReal p) b, ?_⟩
    ext s
    change (∑ i, (realProductFrame n s i : ℂ) * ((frameNormalization n p : ℂ) * b i)) =
      (frameNormalization n p : ℂ) * (∑ i, b i * (realProductFrame n s i : ℂ))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rintro y ⟨b, rfl⟩
    refine ⟨(fun i => (frameNormalization n p : ℂ)⁻¹ * b i : ComplexFrameCoefficient n p), ?_⟩
    ext s
    change (frameNormalization n p : ℂ) *
      (∑ i, ((frameNormalization n p : ℂ)⁻¹ * b i) * (realProductFrame n s i : ℂ)) =
      ∑ i, (realProductFrame n s i : ℂ) * b i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hne : (frameNormalization n p : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (frameNormalization_pos n p).ne'
    field_simp

theorem complexFrameCoefficientEmbedding_range_eq_projection (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    (complexFrameCoefficientEmbedding n p).range =
      (complexMatrixPiLpCLM (ENNReal.ofReal p) (complexTensorFrameProjection n)).range :=
  (complexFrameCoefficientEmbedding_range_eq n p).trans
    (complexTensorFrameProjection_range_eq (ENNReal.ofReal p) n).symm

def complexFrameCoefficientRangeEquiv (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    ComplexFrameCoefficient n p ≃ₗᵢ[ℂ]
      (complexMatrixPiLpCLM (ENNReal.ofReal p) (complexTensorFrameProjection n)).range :=
  (complexFrameCoefficientIsometry n p).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (complexFrameCoefficientEmbedding_range_eq_projection n p))

end ComplementedSubspace
