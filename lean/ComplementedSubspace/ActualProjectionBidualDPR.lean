import ComplementedSubspace.RecursiveDiagonalBidualDPR
import ComplementedSubspace.ActualProjectionDPR
import ComplementedSubspace.RecursiveProjection

/-! Bidual DPR obstructions for the actual existential alternating projector. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {η : ℝ} (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)
  (T : Ambient s.toBlockParameters →L[ℝ] Ambient s.toBlockParameters)
  (hcoords : ∀ x j, T x j = s.alternatingBlockProjection j (x j))

include hcoords

theorem actualProjection_range_bidual_chiDPR_eq_top :
    HasInfiniteBidualDPR T.range := by
  have hbound := block_norm_le_of_coordinate_formula 2 T s.alternatingBlockProjection hcoords
  have hEq := eq_lpDiagonal_of_coordinate_formula 2 T s.alternatingBlockProjection hcoords
  have h := recursiveDiagonalRange_bidual_chiDPR_eq_top s s.alternatingBlockProjection
    (norm_nonneg T) hbound s.alternatingBlockProjection_idempotent
    Even (fun j hj => s.frameCoefficientEvenRangeEquiv j hj) even_indices_unbounded
  rw [← hEq] at h
  exact h

theorem actualProjection_complement_range_bidual_chiDPR_eq_top :
    HasInfiniteBidualDPR
      (ContinuousLinearMap.id ℝ (Ambient s.toBlockParameters) - T).range := by
  let Tc := ContinuousLinearMap.id ℝ (Ambient s.toBlockParameters) - T
  let Q := fun j => ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) - s.alternatingBlockProjection j
  have hcoordsc : ∀ x j, Tc x j = Q j (x j) :=
    complement_coordinate_formula 2 T s.alternatingBlockProjection hcoords
  have hbound := block_norm_le_of_coordinate_formula 2 Tc Q hcoordsc
  have hEq := eq_lpDiagonal_of_coordinate_formula 2 Tc Q hcoordsc
  have hIdem : ∀ j, (Q j).comp (Q j) = Q j := fun j =>
    complement_idempotent _ (s.alternatingBlockProjection_idempotent j)
  have h := recursiveDiagonalRange_bidual_chiDPR_eq_top s Q (norm_nonneg Tc) hbound hIdem
    (fun j => ¬ Even j) (fun j hj => s.frameCoefficientOddComplementRangeEquiv j hj)
    odd_indices_unbounded
  rw [← hEq] at h
  exact h

end ComplementedSubspace
