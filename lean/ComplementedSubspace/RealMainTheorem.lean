import ComplementedSubspace.ActualProjectionDPR
import ComplementedSubspace.ActualProjectionDualDPR
import ComplementedSubspace.AmbientUniformConvex
import ComplementedSubspace.AmbientFiniteApproximation
import ComplementedSubspace.ProjectionCorollaries

/-! Assembly of the real main theorem from the actual recursive construction. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

theorem realMainTheorem : RealMainTheoremStatement := by
  intro ρ hρ
  obtain ⟨η, hη, P, hPP, hP1, hP, hPc1, hPc, hcoords⟩ :=
    exists_recursive_alternatingProjection_near_one (B := 1 + ρ) (by linarith)
  let s := recursiveFrameSelection hη
  refine ⟨s.toBlockParameters, inferInstance, inferInstance,
    ambient_hasRealBanachLatticeOrder s.toBlockParameters, P, hPP, hP, hPc, ?_, ?_⟩
  · exact hasSeparatedRange_of_DPR_obstructions P hPP
      (ambient_chiGL_le_one s.toBlockParameters) (ambientDual_chiGL_le_one s.toBlockParameters)
      (actualProjection_range_chiDPR_eq_top s P hcoords)
      (actualProjection_range_dual_chiDPR_eq_top s P hcoords)
  · exact hasSeparatedRange_of_DPR_obstructions
      (ContinuousLinearMap.id ℝ (Ambient s.toBlockParameters) - P) (complement_idempotent P hPP)
      (ambient_chiGL_le_one s.toBlockParameters) (ambientDual_chiGL_le_one s.toBlockParameters)
      (actualProjection_complement_range_chiDPR_eq_top s P hcoords)
      (actualProjection_complement_range_dual_chiDPR_eq_top s P hcoords)

end ComplementedSubspace
