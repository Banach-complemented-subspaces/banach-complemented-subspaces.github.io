import ComplementedSubspace.LocalHilbertEmbeddedRenorm
import ComplementedSubspace.LocalHilbertHeadRenorm
import ComplementedSubspace.RecursiveTailHilbert
import ComplementedSubspace.LpHeadTail

/-!
# Actual recursive coordinate kernels: the dual-subspace-dual estimate

The coordinate kernel is only required to embed isometrically in its finite
head and tail product. We renorm the whole product, then use the actual image
of the kernel. The image inherits the parallelogram estimate, so no onto
product reconstruction or reflexivity assumption is needed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

theorem recursiveProfile_embedding_dual_subspaces {η : ℝ}
    (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)
    (S : ∀ i : ℕ, Submodule ℝ (Block s.toBlockParameters i)) (j : ℕ)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (i : W →ₗᵢ[ℝ] WithLp 2
      (lp (fun k : Fin j => S k.val) 2 × RecursiveProfileTail s S j)) :
    DualSubspacesLocallyHilbertWithin (StrongDual ℝ W)
      (3 * 2 ^ (s.block j).order) (2 * s.headBound j) := by
  obtain ⟨p, hp⟩ := recursiveProfile_finiteHead_hilbertModel s S j
  have hD : 1 ≤ s.headBound j := (by norm_num : (1 : ℝ) ≤ 2).trans (s.headBound_ge_two j)
  let ν := recursiveLocalHilbertThreshold (3 * 2 ^ (s.block j).order)
  have hν : 1 ≤ ν := (recursiveLocalHilbertThreshold_gt_one _).le
  have hhead : ApproxParallelogram (fun x : p.Space => ‖x‖) 1 := by
    intro x y
    simpa only [mul_one] using (parallelogram_law_with_norm ℝ x y).le
  have hpar : ApproxParallelogram
      (fun x : WithLp 2 (p.Space × RecursiveProfileTail s S j) => ‖x‖) ν :=
    (hhead.mono hν).prodL2 (recursiveProfileTail_approxParallelogram s S j)
  have hgood : ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G],
      ApproxParallelogram (fun x : G => ‖x‖) ν →
        LocallyHilbertWithin G (3 * 2 ^ (s.block j).order) 2 := by
    intro G _ _ hG
    exact recursiveLocalHilbertThreshold_spec _ G hG
  have h := embedded_renorm_dual_subspace_dual_localHilbert (zero_le_one.trans hD)
    hgood i (headTailRenormEquiv p hD hp) (headTailRenormEquiv_norm_le p hD hp)
    (headTailRenormEquiv_symm_norm_le p hD hp) hpar
  simpa only [mul_comm (s.headBound j) 2] using h

/-- The estimate for a coordinate kernel in an arbitrary inherited profile. -/
theorem recursiveProfile_kernel_dual_subspaces {η : ℝ}
    (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)
    (S : ∀ i : ℕ, Submodule ℝ (Block s.toBlockParameters i)) (j : ℕ) :
    DualSubspacesLocallyHilbertWithin
      (StrongDual ℝ (lp.evalCLM ℝ (fun i => S i) 2 j).ker)
      (3 * 2 ^ (s.block j).order) (2 * s.headBound j) :=
  recursiveProfile_embedding_dual_subspaces s S j (lpKernelHeadTailIsometry j)

/-- The exact inherited kernel of an actual diagonal projection range has
the dual local estimate used by the main dual DPR obstruction. -/
theorem recursiveDiagonalRange_kernel_dual_subspaces {η : ℝ}
    (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)
    (P : ∀ i, Block s.toBlockParameters i →L[ℝ] Block s.toBlockParameters i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i) (j : ℕ) :
    DualSubspaceDualHilbertWithin
      (lpDiagonalRangeEval P hC hP hIdem j).ker
      (3 * 2 ^ (s.block j).order) (2 * s.headBound j) :=
  recursiveProfile_embedding_dual_subspaces s (fun i => (P i).range) j
    (W := (lpDiagonalRangeEval P hC hP hIdem j).ker)
    (lpDiagonalRangeKernelHeadTailIsometry P hC hP hIdem j)

end ComplementedSubspace
