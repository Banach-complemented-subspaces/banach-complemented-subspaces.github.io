import ComplementedSubspace.ComplexTensorProjection
import ComplementedSubspace.ReindexedFrameProjection

/-! Complex tensor projections on the actual finite coordinate sets of the
complex ambient, together with the isometric range identification. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

section Transport
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

def scalarIsometricConjugate (e : E ≃ₗᵢ[𝕜] F) (P : E →L[𝕜] E) : F →L[𝕜] F :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (P.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem scalarIsometricConjugate_apply
    (e : E ≃ₗᵢ[𝕜] F) (P : E →L[𝕜] E) (x : F) :
    scalarIsometricConjugate e P x = e (P (e.symm x)) := rfl

theorem scalarIsometricConjugate_norm (e : E ≃ₗᵢ[𝕜] F) (P : E →L[𝕜] E) :
    ‖scalarIsometricConjugate e P‖ = ‖P‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa using P.le_opNorm (e.symm x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa using (scalarIsometricConjugate e P).le_opNorm (e x)

theorem scalarIsometricConjugate_idempotent (e : E ≃ₗᵢ[𝕜] F) (P : E →L[𝕜] E)
    (hP : P.comp P = P) :
    (scalarIsometricConjugate e P).comp (scalarIsometricConjugate e P) =
      scalarIsometricConjugate e P := by
  ext x
  simpa only [ContinuousLinearMap.comp_apply, scalarIsometricConjugate_apply,
    e.symm_apply_apply] using congrArg (fun T : E →L[𝕜] E => e (T (e.symm x))) hP

theorem scalarIsometricConjugate_range (e : E ≃ₗᵢ[𝕜] F) (P : E →L[𝕜] E) :
    P.range.map e.toLinearEquiv.toLinearMap = (scalarIsometricConjugate e P).range := by
  apply le_antisymm
  · rintro x ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨e z, ?_⟩
    simp
  · rintro x ⟨y, rfl⟩
    exact ⟨P (e.symm y), ⟨e.symm y, rfl⟩, rfl⟩

def scalarIsometricConjugateRangeEquiv (e : E ≃ₗᵢ[𝕜] F) (P : E →L[𝕜] E) :
    P.range ≃ₗᵢ[𝕜] (scalarIsometricConjugate e P).range :=
  (LinearIsometryEquiv.submoduleMap P.range e).trans
    (LinearIsometryEquiv.ofEq _ _ (scalarIsometricConjugate_range e P))

end Transport

def complexFramePiLpEquivFin (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    PiLp p (fun _ : FrameIndex n => ℂ) ≃ₗᵢ[ℂ] PiLp p (fun _ : Fin (4 ^ n) => ℂ) :=
  LinearIsometryEquiv.piLpCongrLeft p ℂ ℂ (frameIndexEquivFin n)

def complexFinTensorProjection (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    PiLp p (fun _ : Fin (4 ^ n) => ℂ) →L[ℂ] PiLp p (fun _ : Fin (4 ^ n) => ℂ) :=
  scalarIsometricConjugate (complexFramePiLpEquivFin p n)
    (complexMatrixPiLpCLM p (complexTensorFrameProjection n))

theorem complexFinTensorProjection_idempotent (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    (complexFinTensorProjection p n).comp (complexFinTensorProjection p n) =
      complexFinTensorProjection p n :=
  scalarIsometricConjugate_idempotent _ _ (complexTensorFrameProjection_clm_idempotent p n)

theorem complexFinTensorProjection_norm_le_exp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hp3 : p ≤ 3) (n : ℕ) :
    ‖complexFinTensorProjection (ENNReal.ofReal p) n‖ ≤
      Real.exp (18 * (n : ℝ) * (p - 2) ^ 2) := by
  rw [complexFinTensorProjection, scalarIsometricConjugate_norm]
  exact complexTensorFrameProjection_norm_le_exp hp hp3 n

theorem one_le_complexFinTensorProjection_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    1 ≤ ‖complexFinTensorProjection p n‖ := by
  rw [complexFinTensorProjection, scalarIsometricConjugate_norm]
  exact one_le_complexTensorFrameProjection_norm p n

end ComplementedSubspace
