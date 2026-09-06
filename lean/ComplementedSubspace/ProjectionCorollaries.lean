import ComplementedSubspace.GLDualRetraction
import ComplementedSubspace.LatticeNonisomorphism
import ComplementedSubspace.SchauderDPR
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-! Assemble the analytic conclusions from explicit DPR obstructions. The
obstructions themselves are hypotheses supplied by the block construction. -/

noncomputable section
namespace ComplementedSubspace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem completeSpace_projection_range [CompleteSpace X]
    (P : X →L[ℝ] X) (hP : P.comp P = P) : CompleteSpace ↥P.range :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range (p := P) hP).completeSpace_coe

theorem chiGL_range_le_projection_norm_all (P : X →L[ℝ] X)
    (hP : P.comp P = P) (hX : chiGL X ≤ 1) : chiGL ↥P.range ≤ ‖P‖ₑ := by
  rcases subsingleton_or_nontrivial ↥P.range with hZ | hZ
  · letI := hZ
    rw [chiGL_eq_zero_of_subsingleton]
    exact zero_le
  · letI := hZ
    exact chiGL_range_le_projection_norm P hP hX

theorem hasSeparatedRange_of_DPR_obstructions (P : X →L[ℝ] X)
    (hP : P.comp P = P) (hX : chiGL X ≤ 1) (hXD : chiGL (StrongDual ℝ X) ≤ 1)
    (hZ : chiDPR ↥P.range = ⊤) (hZD : chiDPR (StrongDual ℝ ↥P.range) = ⊤) :
    HasSeparatedRange P :=
  ⟨chiGL_range_le_projection_norm_all P hP hX, hZ,
    chiGL_dual_range_le_projection_norm P hP hXD, hZD⟩

/-- All four negative conclusions in the real unconditional-basis corollary.
The third DPR hypothesis is the separate bidual obstruction needed for the
universal nonlattice assertion about the range dual. -/
theorem corollary_negations_of_DPR_obstructions [CompleteSpace X]
    (hZ : chiDPR X = ⊤)
    (hZD : chiDPR (StrongDual ℝ X) = ⊤)
    (hZDD : chiDPR (StrongDual ℝ (StrongDual ℝ X)) = ⊤) :
    ¬ HasUnconditionalSchauderBasis ℝ X ∧
    ¬ HasUnconditionalSchauderBasis ℝ (StrongDual ℝ X) ∧
    ¬ IsIsomorphicToRealBanachLattice X ∧
    ¬ IsIsomorphicToRealBanachLattice (StrongDual ℝ X) := by
  exact ⟨not_hasUnconditionalSchauderBasis_of_chiDPR_top hZ,
    not_hasUnconditionalSchauderBasis_of_chiDPR_top hZD,
    not_isomorphic_to_realBanachLattice_of_dual_DPR_top hZD,
    not_isomorphic_to_realBanachLattice_of_dual_DPR_top hZDD⟩

end ComplementedSubspace
