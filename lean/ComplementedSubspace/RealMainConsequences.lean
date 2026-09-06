import ComplementedSubspace.RealMainTheorem
import ComplementedSubspace.ActualProjectionBidualDPR
import ComplementedSubspace.AmbientSchauder

/-! Real corollary and separable nonprimarity for the actual recursive construction.
The nonlattice assertion for the range dual uses the separately proved bidual
DPR obstruction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

def ambientBanachModel (a : BlockParameters) : BanachModel.{0} ℝ where
  Carrier := Ambient a
  normedGroup := inferInstance
  normedSpace := inferInstance
  completeSpace := inferInstance

theorem realCorollary : RealCorollaryStatement := by
  intro ρ hρ
  obtain ⟨η, hη, P, hPP, hP1, hP, hPc1, hPc, hcoords⟩ :=
    exists_recursive_alternatingProjection_near_one (B := 1 + ρ) (by linarith)
  let s := recursiveFrameSelection hη
  letI : CompleteSpace P.range := completeSpace_projection_range P hPP
  have hn := @corollary_negations_of_DPR_obstructions P.range
    (inferInstance : NormedAddCommGroup P.range)
    (inferInstance : NormedSpace ℝ P.range)
    (completeSpace_projection_range P hPP)
    (actualProjection_range_chiDPR_eq_top s P hcoords)
    (actualProjection_range_dual_chiDPR_eq_top s P hcoords)
    (actualProjection_range_bidual_chiDPR_eq_top s P hcoords)
  exact ⟨ambientBanachModel s.toBlockParameters,
    ambient_hasOneUnconditionalSchauderBasis s.toBlockParameters,
    P, hPP, hP, hn⟩

theorem realUnconditionalCorollary : UnconditionalCorollaryStatement ℝ := by
  intro ρ hρ
  obtain ⟨X, hX, P, hPP, hP, hZ, hZD, hZlat, hZDlat⟩ := realCorollary ρ hρ
  exact ⟨X, hX, P, hPP, hP, hZ, hZD⟩

theorem separableNonprimarity_of_realMainTheorem (hmain : RealMainTheoremStatement) :
    SeparableNonprimarityStatement := by
  intro ρ hρ
  obtain ⟨a, hsep, huc, hlat, P, hPP, hP, hPc, hZ, hZc⟩ := hmain ρ hρ
  refine ⟨ambientBanachModel a, hsep, hlat, ?_,
    ambient_hasOneUnconditionalSchauderBasis a, P, hPP, hP, hPc, ?_, ?_⟩
  · exact ⟨ambientBanachModel a, huc, ⟨ContinuousLinearEquiv.refl ℝ (Ambient a)⟩⟩
  · exact not_isomorphic_to_realBanachLattice_of_dual_DPR_top hZ.2.2.2
  · exact not_isomorphic_to_realBanachLattice_of_dual_DPR_top hZc.2.2.2

theorem realSeparableNonprimarity : SeparableNonprimarityStatement :=
  separableNonprimarity_of_realMainTheorem realMainTheorem

end ComplementedSubspace
