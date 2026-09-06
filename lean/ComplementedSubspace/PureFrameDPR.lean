import ComplementedSubspace.RecursiveDiagonalDPR
import ComplementedSubspace.RecursiveDiagonalDualDPR
import ComplementedSubspace.LpUniformEquiv
import ComplementedSubspace.DPRIsomorphism

/-! The real coefficient profile has infinite DPR, as does its real continuous
dual. This endpoint uses every block frame range, without alternating parity. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

section UniformIsometry
variable {ι 𝕜 : Type*} {E F : ι → Type*} [NontriviallyNormedField 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

def lpUniformIsometryEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) : lp E p ≃ₗᵢ[𝕜] lp F p := by
  let e' := lpUniformEquiv p (fun i => (e i).toContinuousLinearEquiv)
    zero_le_one (fun i => (e i).toLinearIsometry.norm_toContinuousLinearMap_le)
    zero_le_one (fun i => (e i).symm.toLinearIsometry.norm_toContinuousLinearMap_le)
  refine { e'.toLinearEquiv with norm_map' := ?_ }
  intro x
  have h := lpUniformEquiv_norm_bounds p (fun i => (e i).toContinuousLinearEquiv)
    zero_le_one (fun i => (e i).toLinearIsometry.norm_toContinuousLinearMap_le)
    zero_le_one (fun i => (e i).symm.toLinearIsometry.norm_toContinuousLinearMap_le) x
  simp only [one_mul] at h
  exact le_antisymm h.1 h.2

@[simp] theorem lpUniformIsometryEquiv_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) (x : lp E p) (i : ι) :
    lpUniformIsometryEquiv p e x i = e i (x i) := rfl

end UniformIsometry

section Transport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem chiDPR_eq_top_of_continuousLinearEquiv (e : E ≃L[ℝ] F)
    (hF : chiDPR F = ⊤) : chiDPR E = ⊤ := by
  by_contra hE
  have hfin : HasDPRLocalUnconditionalStructure E := lt_top_iff_ne_top.mpr hE
  have h := hfin.of_continuousLinearEquiv e
  change chiDPR F < ⊤ at h
  rw [hF] at h
  exact (lt_irrefl _ h)

end Transport

namespace RecursiveFrameSelection
variable {η : ℝ} (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)

abbrev PureFrameCoefficientProfile :=
  lp (fun j => FrameCoefficient (s.block j).order (s.block j).exponent) 2

def pureFrameProjection : Ambient s.toBlockParameters →L[ℝ] Ambient s.toBlockParameters :=
  lpDiagonal 2 s.blockFrameProjection (Real.exp_pos _).le s.blockFrameProjection_norm_le

theorem pureFrameProjection_idempotent :
    s.pureFrameProjection.comp s.pureFrameProjection = s.pureFrameProjection :=
  lpDiagonal_idempotent 2 s.blockFrameProjection (Real.exp_pos _).le
    s.blockFrameProjection_norm_le s.blockFrameProjection_idempotent

theorem pureFrameProjection_range_chiDPR_eq_top : chiDPR s.pureFrameProjection.range = ⊤ :=
  recursiveDiagonalRange_chiDPR_eq_top s s.blockFrameProjection (Real.exp_pos _).le
    s.blockFrameProjection_norm_le s.blockFrameProjection_idempotent
    (fun _ => True) (fun j _ => s.frameCoefficientBlockRangeEquiv j)
    (fun N => ⟨N, le_rfl, trivial⟩)

theorem pureFrameProjection_range_dual_chiDPR_eq_top :
    chiDPR (StrongDual ℝ s.pureFrameProjection.range) = ⊤ :=
  recursiveDiagonalRange_dual_chiDPR_eq_top s s.blockFrameProjection (Real.exp_pos _).le
    s.blockFrameProjection_norm_le s.blockFrameProjection_idempotent
    (fun _ => True) (fun j _ => s.frameCoefficientBlockRangeEquiv j)
    (fun N => ⟨N, le_rfl, trivial⟩)

def pureFrameCoefficientRangeEquiv :
    s.PureFrameCoefficientProfile ≃ₗᵢ[ℝ] s.pureFrameProjection.range :=
  (lpUniformIsometryEquiv 2 s.frameCoefficientBlockRangeEquiv).trans
    (lpDiagonalRangeEquiv s.blockFrameProjection (Real.exp_pos _).le
      s.blockFrameProjection_norm_le s.blockFrameProjection_idempotent)

theorem pureFrameCoefficientProfile_chiDPR_eq_top : chiDPR s.PureFrameCoefficientProfile = ⊤ :=
  chiDPR_eq_top_of_continuousLinearEquiv s.pureFrameCoefficientRangeEquiv.toContinuousLinearEquiv
    s.pureFrameProjection_range_chiDPR_eq_top

theorem pureFrameCoefficientProfile_dual_chiDPR_eq_top :
    chiDPR (StrongDual ℝ s.PureFrameCoefficientProfile) = ⊤ :=
  chiDPR_eq_top_of_continuousLinearEquiv
    (realDualIsometryEquiv s.pureFrameCoefficientRangeEquiv).toContinuousLinearEquiv
    s.pureFrameProjection_range_dual_chiDPR_eq_top

end RecursiveFrameSelection
end ComplementedSubspace
