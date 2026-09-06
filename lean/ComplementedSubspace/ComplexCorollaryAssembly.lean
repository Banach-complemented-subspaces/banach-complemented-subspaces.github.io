import ComplementedSubspace.ComplexAmbientSchauder
import ComplementedSubspace.ComplexRecursiveProjection
import ComplementedSubspace.ComplexRealDPR
import ComplementedSubspace.PureFrameDPR
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-! Assemble the complex theorem from a genuine equivalence of each complete
projection range with the verified real coefficient profile. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

def complexAmbientBanachModel (a : BlockParameters) : BanachModel.{0} ℂ where
  Carrier := ComplexAmbient a
  normedGroup := inferInstance
  normedSpace := inferInstance
  completeSpace := inferInstance

theorem complexCorollary_of_recursive_range_equivalences
    (h : ∀ {η : ℝ} (s : RecursiveFrameSelection η recursiveFrameExponentTolerance),
      Nonempty (s.predecessorComplexProjection.range ≃L[ℝ] s.PureFrameCoefficientProfile)) :
    ComplexCorollaryStatement := by
  intro ρ hρ
  obtain ⟨η, hη, hP⟩ :=
    exists_recursive_predecessorComplexProjection_near_one (B := 1 + ρ) (by linarith)
  let s := recursiveFrameSelection hη
  obtain ⟨e⟩ := h s
  letI : CompleteSpace s.predecessorComplexProjection.range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (p := s.predecessorComplexProjection) s.predecessorComplexProjection_idempotent).completeSpace_coe
  have hn : ¬ HasUnconditionalSchauderBasis ℂ s.predecessorComplexProjection.range :=
    not_hasComplexUnconditionalSchauderBasis_of_real_equiv
      (E := s.predecessorComplexProjection.range)
      e s.pureFrameCoefficientProfile_chiDPR_eq_top
  have hnd : ¬ HasUnconditionalSchauderBasis ℂ (StrongDual ℂ s.predecessorComplexProjection.range) :=
    not_hasComplexUnconditionalSchauderBasis_dual_of_real_equiv
      (E := s.predecessorComplexProjection.range)
      e s.pureFrameCoefficientProfile_dual_chiDPR_eq_top
  exact ⟨complexAmbientBanachModel s.predecessorBlockParameters,
    complexAmbient_hasOneUnconditionalSchauderBasis s.predecessorBlockParameters,
    s.predecessorComplexProjection, s.predecessorComplexProjection_idempotent, hP, hn, hnd⟩

end ComplementedSubspace
