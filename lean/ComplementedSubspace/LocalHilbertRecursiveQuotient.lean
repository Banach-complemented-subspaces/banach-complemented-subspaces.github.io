import ComplementedSubspace.LocalHilbertHeadRenorm
import ComplementedSubspace.RecursiveParameters

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

/-- The quotient-type dual estimate at precisely the threshold already used
by the recursive parameters. No new choice of parameter sequence is needed. -/
theorem recursive_headTail_dual_subspace_dual_localHilbert
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℕ) {D : ℝ} (hD : 1 ≤ D) (hE : HasHilbertNormWithin E D)
    (hF : ApproxParallelogram (fun x : F => ‖x‖) (recursiveLocalHilbertThreshold d)) :
    DualSubspacesLocallyHilbertWithin (StrongDual ℝ (WithLp 2 (E × F))) d (D * 2) := by
  apply headTail_dual_subspace_dual_localHilbert hD
    (recursiveLocalHilbertThreshold_gt_one d).le _ hE hF
  intro G _ _ hG
  exact recursiveLocalHilbertThreshold_spec d G hG

end ComplementedSubspace
