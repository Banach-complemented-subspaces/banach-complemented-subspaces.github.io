import ComplementedSubspace.RecursiveTailHilbert
import ComplementedSubspace.LocalHilbertSumDual
import ComplementedSubspace.LpHeadTail

/-! Actual coordinate kernels have the local Hilbert control needed for
the infinite DPR obstruction, with no loss beyond the recursive head bound. -/
noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

theorem locallyHilbert_of_isometricEmbedding_prodL2 {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {d : ℕ} {D : ℝ} (hD : 2 ≤ D)
    (e : E →ₗᵢ[ℝ] WithLp 2 (F × G)) (hF : HasHilbertNormWithin F D)
    (hG : LocallyHilbertWithin G d 2) : LocallyHilbertWithin E d D := by
  intro V _ hV
  let U := e.toContinuousLinearMap.comp V.subtypeL
  let A := (WithLp.fstL 2 ℝ F G).comp U
  let B := (WithLp.sndL 2 ℝ F G).comp U
  apply localHilbert_of_norm_sq_decomposition hD hV hF hG A B
  intro x
  change ‖x‖ ^ 2 = ‖(e (x : E)).fst‖ ^ 2 + ‖(e (x : E)).snd‖ ^ 2
  rw [← WithLp.prod_norm_sq_eq_of_L2, e.norm_map]
  rfl

theorem recursiveProfile_kernel_locallyHilbert {η : ℝ}
    (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)
    (S : ∀ i : ℕ, Submodule ℝ (Block s.toBlockParameters i)) (j : ℕ) :
    LocallyHilbertWithin (lp.evalCLM ℝ (fun i => S i) 2 j).ker
      (3 * 2 ^ (s.block j).order) (s.headBound j) := by
  have hD : 2 ≤ s.headBound j := by
    have h := s.headBound_ge_index j
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  exact locallyHilbert_of_isometricEmbedding_prodL2 hD
    (lpKernelHeadTailIsometry (E := fun i => S i) j)
    (recursiveProfile_finiteHead_hasHilbertNormWithin s S j)
    (recursiveProfileTail_locallyHilbert s S j)

/-- The same estimate inside the kernel of a coordinate evaluation on the
actual diagonal projection range, using its inherited norm. -/
theorem recursiveDiagonalRange_kernel_locallyHilbert {η : ℝ}
    (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)
    (P : ∀ i, Block s.toBlockParameters i →L[ℝ] Block s.toBlockParameters i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i) (j : ℕ) :
    LocallyHilbertWithin (lpDiagonalRangeEval P hC hP hIdem j).ker
      (3 * 2 ^ (s.block j).order) (s.headBound j) := by
  have hD : 2 ≤ s.headBound j := by
    have h := s.headBound_ge_index j
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  exact locallyHilbert_of_isometricEmbedding_prodL2 hD
    (lpDiagonalRangeKernelHeadTailIsometry P hC hP hIdem j)
    (recursiveProfile_finiteHead_hasHilbertNormWithin s (fun i => (P i).range) j)
    (recursiveProfileTail_locallyHilbert s (fun i => (P i).range) j)

end ComplementedSubspace
