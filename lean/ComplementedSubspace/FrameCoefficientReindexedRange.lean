import ComplementedSubspace.RecursiveProjection
import ComplementedSubspace.FrameCoefficientRange

/-! Exact coefficient-space identification inside the alternating finite block ranges. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

theorem isometricConjugate_range {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) :
    P.range.map e.toLinearEquiv.toLinearMap = (isometricConjugate e P).range := by
  apply le_antisymm
  · rintro x ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨e z, ?_⟩
    simp
  · rintro x ⟨y, rfl⟩
    exact ⟨P (e.symm y), ⟨e.symm y, rfl⟩, rfl⟩

def isometricConjugateRangeEquiv {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) :
    P.range ≃ₗᵢ[ℝ] (isometricConjugate e P).range :=
  (LinearIsometryEquiv.submoduleMap P.range e).trans
    (LinearIsometryEquiv.ofEq _ _ (isometricConjugate_range e P))

def frameCoefficientFinRangeEquiv (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    FrameCoefficient n p ≃ₗᵢ[ℝ] (finTensorProjection (ENNReal.ofReal p) n).range :=
  (frameCoefficientRangeEquiv n p).trans
    (isometricConjugateRangeEquiv (framePiLpEquivFin (ENNReal.ofReal p) n) _)

namespace RecursiveFrameSelection
variable {η : ℝ} {θ : ℕ → ℝ} (s : RecursiveFrameSelection η θ)

def frameCoefficientBlockRangeEquiv (j : ℕ) :
    FrameCoefficient (s.block j).order (s.block j).exponent ≃ₗᵢ[ℝ] (s.blockFrameProjection j).range :=
  frameCoefficientFinRangeEquiv (s.block j).order (s.block j).exponent

def frameCoefficientEvenRangeEquiv (j : ℕ) (hj : Even j) :
    FrameCoefficient (s.block j).order (s.block j).exponent ≃ₗᵢ[ℝ]
      (s.alternatingBlockProjection j).range :=
  (s.frameCoefficientBlockRangeEquiv j).trans (LinearIsometryEquiv.ofEq _ _ (by
    rw [alternatingBlockProjection, if_pos hj]))

def frameCoefficientOddComplementRangeEquiv (j : ℕ) (hj : ¬ Even j) :
    FrameCoefficient (s.block j).order (s.block j).exponent ≃ₗᵢ[ℝ]
      (ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) - s.alternatingBlockProjection j).range :=
  (s.frameCoefficientBlockRangeEquiv j).trans (LinearIsometryEquiv.ofEq _ _ (by
    rw [alternatingBlockProjection, if_neg hj, sub_sub_cancel]))

end RecursiveFrameSelection
end ComplementedSubspace
