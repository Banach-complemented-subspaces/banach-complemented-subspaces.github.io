import ComplementedSubspace.NormSqSplitting
import ComplementedSubspace.DiagonalFrameSummand

/-! Exact frame-versus-remainder product on the actual diagonal range. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  (P : ∀ i, E i →L[ℝ] E i) {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
  (hIdem : ∀ i, (P i).comp (P i) = P i) (j : ι)
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (e : A ≃ₗᵢ[ℝ] (P j).range)

def diagonalFrameProductEquiv :
    (lpDiagonal 2 P hC hP).range ≃ₗᵢ[ℝ]
      WithLp 2 (A × (lpDiagonalRangeEval P hC hP hIdem j).ker) := by
  let I := diagonalSummandI P hC hP hIdem j e
  let R := diagonalSummandR P hC hP hIdem j e
  let J := diagonalSummandJ P hC hP hIdem j
  let S := diagonalSummandS P hC hP hIdem j
  refine @normSqSplitEquiv A
    (lpDiagonalRangeEval P hC hP hIdem j).ker (lpDiagonal 2 P hC hP).range
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    I R J S ?_ ?_ ?_ ?_ ?_
    (diagonalSummand_norm_sq P hC hP hIdem j e)
  · intro x
    exact congrArg (fun T : A →L[ℝ] A => T x) (diagonalSummand_RI P hC hP hIdem j e)
  · intro x
    apply Subtype.ext
    change lpDiagonalRangeSingle P hC hP hIdem j (e x) -
      lpDiagonalRangeSingle P hC hP hIdem j (lpDiagonalRangeEval P hC hP hIdem j
        (lpDiagonalRangeSingle P hC hP hIdem j (e x))) = 0
    rw [lpDiagonalRangeEval_single, sub_self]
  · intro w
    exact congrArg (fun T => T w) (diagonalSummand_RJ P hC hP hIdem j e)
  · intro w
    exact congrArg (fun T => T w) (diagonalSummand_SJ P hC hP hIdem j)
  · intro z
    have h := congrArg (fun T => T z) (diagonalSummand_JS P hC hP hIdem j e)
    change J (S z) = z - I (R z) at h
    rw [h, add_sub_cancel]

end ComplementedSubspace
