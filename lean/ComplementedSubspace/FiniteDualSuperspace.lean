import ComplementedSubspace.IsometricProductSplitting
import ComplementedSubspace.FiniteBidual
import ComplementedSubspace.LocalHilbertSumDual

/-! The actual dual of a superspace containing a finite dual summand. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

variable {E W Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem isometricProduct_first_range_ne_bot [Nontrivial E]
    (e : Z ≃ₗᵢ[ℝ] WithLp 2 (E × W)) :
    (IsometricProductSplitting.inclusion e).range ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  intro hbot
  have hIx : IsometricProductSplitting.inclusion e x = 0 := by
    have hm : IsometricProductSplitting.inclusion e x ∈
        (IsometricProductSplitting.inclusion e).range := ⟨x, rfl⟩
    rw [hbot] at hm
    exact hm
  have h := congrArg (fun T : E →L[ℝ] E => T x)
    (IsometricProductSplitting.first_inclusion e)
  have hx0 : x = 0 := by
    change IsometricProductSplitting.first e (IsometricProductSplitting.inclusion e x) = x at h
    rw [hIx, map_zero] at h
    exact h.symm
  exact hx hx0

def finiteSuperspaceDualProductEquiv [FiniteDimensional ℝ E]
    (e : Z ≃ₗᵢ[ℝ] WithLp 2 (StrongDual ℝ E × W))
    (F : Submodule ℝ Z) (hIF : (IsometricProductSplitting.inclusion e).range ≤ F) :
    StrongDual ℝ F ≃ₗᵢ[ℝ]
      WithLp 2 (E × StrongDual ℝ (F.map (IsometricProductSplitting.second e).toLinearMap)) := by
  let eF := SuperspaceSplitting.equiv F
    (IsometricProductSplitting.inclusion e) (IsometricProductSplitting.first e)
    (IsometricProductSplitting.tailInclusion e) (IsometricProductSplitting.second e) hIF
    (IsometricProductSplitting.first_inclusion e) (IsometricProductSplitting.tail_second e)
    (IsometricProductSplitting.first_tailInclusion e) (IsometricProductSplitting.second_tailInclusion e)
    (IsometricProductSplitting.inclusion_contracts e) (IsometricProductSplitting.norm_sq e)
  exact ((realDualIsometryEquiv eF).trans
    (prodL2DualEquiv (StrongDual ℝ E)
      (F.map (IsometricProductSplitting.second e).toLinearMap))).trans
    ((finiteBidualEquiv E).symm.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ _))

end ComplementedSubspace
