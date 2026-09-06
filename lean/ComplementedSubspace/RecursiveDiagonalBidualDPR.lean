import ComplementedSubspace.FiniteBidualDPRLower
import ComplementedSubspace.DiagonalFrameProduct
import ComplementedSubspace.LocalHilbertRecursiveKernelDual
import ComplementedSubspace.DPRPredicates

/-! Infinite DPR for the bidual, needed for nonlattice of each range dual. -/

noncomputable section
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

theorem recursiveDiagonalRange_bidual_chiDPR_eq_top {η : ℝ}
    (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)
    (P : ∀ i, Block s.toBlockParameters i →L[ℝ] Block s.toBlockParameters i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i)
    (good : ℕ → Prop)
    (e : ∀ j, good j → FrameCoefficient (s.block j).order (s.block j).exponent ≃ₗᵢ[ℝ]
      (P j).range)
    (hunbounded : ∀ N : ℕ, ∃ j, N ≤ j ∧ good j) :
    HasInfiniteBidualDPR (lpDiagonal 2 P hC hP).range := by
  unfold HasInfiniteBidualDPR HasInfiniteDualDPR
  apply chiDPR_eq_top_of_nnreal_lower_bounds
  intro K
  let K₀ : ℝ≥0 := max 1 K
  obtain ⟨N, hN⟩ := exists_nat_ge (16 * (K₀ : ℝ))
  obtain ⟨j, hNj, hj⟩ := hunbounded N
  let D : ℝ≥0 := ⟨s.headBound j, (by norm_num : (0 : ℝ) ≤ 2).trans (s.headBound_ge_two j)⟩
  have hD : 2 ≤ D := by exact_mod_cast s.headBound_ge_two j
  have hDK : 16 * K₀ ≤ D := by
    have hNj' : (N : ℝ) ≤ j := by exact_mod_cast hNj
    have hindex := s.headBound_ge_index j
    apply NNReal.coe_le_coe.mp
    change 16 * (K₀ : ℝ) ≤ s.headBound j
    linarith
  have hlower := @frame_product_le_chiDPR_bidual
    (lpDiagonal 2 P hC hP).range (lpDiagonalRangeEval P hC hP hIdem j).ker
    (inferInstance : NormedAddCommGroup (lpDiagonal 2 P hC hP).range)
    (inferInstance : NormedSpace ℝ (lpDiagonal 2 P hC hP).range)
    (inferInstance : NormedAddCommGroup (lpDiagonalRangeEval P hC hP hIdem j).ker)
    (inferInstance : NormedSpace ℝ (lpDiagonalRangeEval P hC hP hIdem j).ker)
    (s.block j).order (s.block j).exponent inferInstance (s.block j).two_lt_exponent.le
    (s.block j).exponent_le_three (diagonalFrameProductEquiv P hC hP hIdem j (e j hj))
    D K₀ hD (le_max_left _ _)
    (recursiveDiagonalRange_kernel_dual_subspaces s P hC hP hIdem j)
    hDK (s.overlap_separation j)
  exact (ENNReal.coe_le_coe.mpr (le_max_right (1 : ℝ≥0) K)).trans hlower

end ComplementedSubspace
