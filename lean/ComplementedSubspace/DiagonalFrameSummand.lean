import ComplementedSubspace.LpSubmodule
import ComplementedSubspace.FrameCoefficientReindexedRange

/-! Exact distinguished-frame summands inside the actual infinite diagonal range. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  (P : ∀ i, E i →L[ℝ] E i) {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
  (hIdem : ∀ i, (P i).comp (P i) = P i) (j : ι)
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (e : A ≃ₗᵢ[ℝ] (P j).range)

def diagonalSummandI : A →L[ℝ] (lpDiagonal 2 P hC hP).range :=
  (lpDiagonalRangeSingle P hC hP hIdem j).comp e.toContinuousLinearEquiv.toContinuousLinearMap

def diagonalSummandR : (lpDiagonal 2 P hC hP).range →L[ℝ] A :=
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (lpDiagonalRangeEval P hC hP hIdem j)

def diagonalSummandJ : (lpDiagonalRangeEval P hC hP hIdem j).ker →L[ℝ]
    (lpDiagonal 2 P hC hP).range := (lpDiagonalRangeEval P hC hP hIdem j).ker.subtypeL

def diagonalSummandS : (lpDiagonal 2 P hC hP).range →L[ℝ]
    (lpDiagonalRangeEval P hC hP hIdem j).ker := lpDiagonalRangeRemainder P hC hP hIdem j

theorem diagonalSummand_RI :
    (diagonalSummandR P hC hP hIdem j e).comp (diagonalSummandI P hC hP hIdem j e) =
      ContinuousLinearMap.id ℝ A := by
  ext x
  change e.symm (lpDiagonalRangeEval P hC hP hIdem j
    (lpDiagonalRangeSingle P hC hP hIdem j (e x))) = x
  rw [lpDiagonalRangeEval_single, e.symm_apply_apply]

theorem diagonalSummand_JS :
    (diagonalSummandJ P hC hP hIdem j).comp (diagonalSummandS P hC hP hIdem j) =
      ContinuousLinearMap.id ℝ (lpDiagonal 2 P hC hP).range -
        (diagonalSummandI P hC hP hIdem j e).comp (diagonalSummandR P hC hP hIdem j e) := by
  apply ContinuousLinearMap.ext
  intro x
  change x - lpDiagonalRangeSingle P hC hP hIdem j (lpDiagonalRangeEval P hC hP hIdem j x) =
    x - lpDiagonalRangeSingle P hC hP hIdem j (e (e.symm (lpDiagonalRangeEval P hC hP hIdem j x)))
  rw [e.apply_symm_apply]

theorem diagonalSummand_SJ :
    (diagonalSummandS P hC hP hIdem j).comp (diagonalSummandJ P hC hP hIdem j) =
      ContinuousLinearMap.id ℝ (lpDiagonalRangeEval P hC hP hIdem j).ker := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change (x : (lpDiagonal 2 P hC hP).range) - lpDiagonalRangeSingle P hC hP hIdem j
    (lpDiagonalRangeEval P hC hP hIdem j x.val) = x.val
  rw [show lpDiagonalRangeEval P hC hP hIdem j x.val = 0 from x.property, map_zero, sub_zero]

theorem diagonalSummand_RJ :
    (diagonalSummandR P hC hP hIdem j e).comp (diagonalSummandJ P hC hP hIdem j) = 0 := by
  ext x
  change e.symm (lpDiagonalRangeEval P hC hP hIdem j x.val) = 0
  rw [show lpDiagonalRangeEval P hC hP hIdem j x.val = 0 from x.property, map_zero]

theorem diagonalSummand_norm_sq (x : (lpDiagonal 2 P hC hP).range) :
    ‖x‖ ^ 2 = ‖diagonalSummandR P hC hP hIdem j e x‖ ^ 2 +
      ‖diagonalSummandS P hC hP hIdem j x‖ ^ 2 := by
  change ‖x‖ ^ 2 = ‖e.symm (lpDiagonalRangeEval P hC hP hIdem j x)‖ ^ 2 +
    ‖lpDiagonalRangeRemainder P hC hP hIdem j x‖ ^ 2
  rw [e.symm.norm_map]
  exact lpDiagonalRange_split_norm_sq P hC hP hIdem x j

theorem diagonalSummand_I_norm (x : A) : ‖diagonalSummandI P hC hP hIdem j e x‖ = ‖x‖ := by
  change ‖lpDiagonalRangeSingle P hC hP hIdem j (e x)‖ = ‖x‖
  rw [lpDiagonalRangeSingle_norm, e.norm_map]

theorem diagonalSummand_R_norm_le (x : (lpDiagonal 2 P hC hP).range) :
    ‖diagonalSummandR P hC hP hIdem j e x‖ ≤ ‖x‖ := by
  change ‖e.symm (lpDiagonalRangeEval P hC hP hIdem j x)‖ ≤ ‖x‖
  rw [e.symm.norm_map]
  simpa only [one_mul] using (lpDiagonalRangeEval P hC hP hIdem j).le_of_opNorm_le
    (lpDiagonalRangeEval_norm_le P hC hP hIdem j) x

theorem diagonalSummand_J_norm (x : (lpDiagonalRangeEval P hC hP hIdem j).ker) :
    ‖diagonalSummandJ P hC hP hIdem j x‖ = ‖x‖ := rfl

theorem diagonalSummand_S_norm_le (x : (lpDiagonal 2 P hC hP).range) :
    ‖diagonalSummandS P hC hP hIdem j x‖ ≤ ‖x‖ :=
  lpDiagonalRangeRemainder_apply_norm_le P hC hP hIdem j x

end ComplementedSubspace
