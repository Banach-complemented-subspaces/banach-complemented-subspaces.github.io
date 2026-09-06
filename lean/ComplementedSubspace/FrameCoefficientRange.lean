import ComplementedSubspace.FrameCoefficient

/-! # Exact isometric identification with the constructed projection range -/

noncomputable section
open scoped BigOperators ENNReal

namespace ComplementedSubspace

theorem frameCoefficientEmbedding_range_eq (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    (frameCoefficientEmbedding n p).range =
      (matrixPiLpCLM (ENNReal.ofReal p) (realProductFrame n)).range := by
  apply le_antisymm
  · rintro y ⟨b, rfl⟩
    refine ⟨frameNormalization n p • WithLp.toLp (ENNReal.ofReal p) b, ?_⟩
    ext s
    change (∑ i, realProductFrame n s i * (frameNormalization n p * b i)) =
      frameNormalization n p * (∑ i, b i * realProductFrame n s i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rintro y ⟨b, rfl⟩
    refine ⟨(fun i => (frameNormalization n p)⁻¹ * b i : FrameCoefficient n p), ?_⟩
    ext s
    change frameNormalization n p *
      (∑ i, ((frameNormalization n p)⁻¹ * b i) * realProductFrame n s i) =
      ∑ i, realProductFrame n s i * b i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hne := ne_of_gt (frameNormalization_pos n p)
    field_simp

theorem frameCoefficientEmbedding_range_eq_projection (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    (frameCoefficientEmbedding n p).range =
      (matrixPiLpCLM (ENNReal.ofReal p) (tensorFrameProjection n)).range :=
  (frameCoefficientEmbedding_range_eq n p).trans
    (tensorFrameProjection_range_eq (ENNReal.ofReal p) n).symm

/-- The coefficient space is exactly isometric to the projection range with
its inherited counting-PiLp norm. -/
def frameCoefficientRangeEquiv (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    FrameCoefficient n p ≃ₗᵢ[ℝ]
      (matrixPiLpCLM (ENNReal.ofReal p) (tensorFrameProjection n)).range :=
  (frameCoefficientIsometry n p).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (frameCoefficientEmbedding_range_eq_projection n p))

end ComplementedSubspace
