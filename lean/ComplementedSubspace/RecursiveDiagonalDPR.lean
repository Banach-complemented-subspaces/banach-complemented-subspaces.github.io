import ComplementedSubspace.InfiniteFrameObstruction
import ComplementedSubspace.RecursiveKernelHilbert
import ComplementedSubspace.DiagonalFrameSummand

/-! The recursive block construction forces infinite DPR in actual diagonal ranges. -/

noncomputable section
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 300000

namespace ComplementedSubspace

theorem recursiveDiagonalRange_chiDPR_eq_top {η : ℝ}
    (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)
    (P : ∀ i, Block s.toBlockParameters i →L[ℝ] Block s.toBlockParameters i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i)
    (good : ℕ → Prop)
    (e : ∀ j, good j → FrameCoefficient (s.block j).order (s.block j).exponent ≃ₗᵢ[ℝ]
      (P j).range)
    (hunbounded : ∀ N : ℕ, ∃ j, N ≤ j ∧ good j) :
    chiDPR (lpDiagonal 2 P hC hP).range = ⊤ := by
  apply chiDPR_eq_top_of_nnreal_lower_bounds
  intro K
  let K₀ : ℝ≥0 := max 1 K
  obtain ⟨N, hN⟩ := exists_nat_ge (8 * (K₀ : ℝ))
  obtain ⟨j, hNj, hj⟩ := hunbounded N
  let D : ℝ≥0 := ⟨s.headBound j, (by norm_num : (0 : ℝ) ≤ 2).trans (s.headBound_ge_two j)⟩
  have hD : 2 ≤ D := by exact_mod_cast s.headBound_ge_two j
  have hDK : 8 * K₀ ≤ D := by
    have hNj' : (N : ℝ) ≤ j := by exact_mod_cast hNj
    have hindex := s.headBound_ge_index j
    change 8 * K₀ ≤ (⟨s.headBound j, _⟩ : ℝ≥0)
    apply NNReal.coe_le_coe.mp
    change 8 * (K₀ : ℝ) ≤ s.headBound j
    linarith
  -- Fix every normed-space instance before specializing to the actual range
  -- and coordinate kernel; otherwise the two subtype paths unfold repeatedly.
  have hlower := @frame_block_le_chiDPR
    (lpDiagonal 2 P hC hP).range (lpDiagonalRangeEval P hC hP hIdem j).ker
    (inferInstance : NormedAddCommGroup (lpDiagonal 2 P hC hP).range)
    (inferInstance : NormedSpace ℝ (lpDiagonal 2 P hC hP).range)
    (inferInstance : NormedAddCommGroup (lpDiagonalRangeEval P hC hP hIdem j).ker)
    (inferInstance : NormedSpace ℝ (lpDiagonalRangeEval P hC hP hIdem j).ker)
    (s.block j).order (s.block j).exponent inferInstance (s.block j).two_lt_exponent.le
    (s.block j).exponent_le_three
    (diagonalSummandI P hC hP hIdem j (e j hj))
    (diagonalSummandR P hC hP hIdem j (e j hj))
    (diagonalSummandJ P hC hP hIdem j)
    (diagonalSummandS P hC hP hIdem j)
    (diagonalSummand_RI P hC hP hIdem j (e j hj))
    (diagonalSummand_JS P hC hP hIdem j (e j hj))
    (diagonalSummand_norm_sq P hC hP hIdem j (e j hj))
    (fun x => (diagonalSummand_I_norm P hC hP hIdem j (e j hj) x).le)
    (diagonalSummand_R_norm_le P hC hP hIdem j (e j hj))
    (fun x => (diagonalSummand_J_norm P hC hP hIdem j x).le)
    (diagonalSummand_S_norm_le P hC hP hIdem j)
    D K₀ hD (le_max_left _ _)
    (recursiveDiagonalRange_kernel_locallyHilbert s P hC hP hIdem j)
    hDK (s.overlap_separation j)
  exact (ENNReal.coe_le_coe.mpr (le_max_right (1 : ℝ≥0) K)).trans hlower

theorem even_indices_unbounded (N : ℕ) : ∃ j, N ≤ j ∧ Even j := by
  exact ⟨2 * N, by omega, ⟨N, by omega⟩⟩

theorem odd_indices_unbounded (N : ℕ) : ∃ j, N ≤ j ∧ ¬ Even j := by
  refine ⟨2 * N + 1, by omega, ?_⟩
  rintro ⟨k, hk⟩
  omega

end ComplementedSubspace
