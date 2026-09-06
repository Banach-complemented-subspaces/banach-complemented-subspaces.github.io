import ComplementedSubspace.DPRtoGL
import Mathlib.Tactic.Linarith

/-!
# Quantitative transport of finite unconditional bases

Transport uses continuous linear equivalences and the original norms. It is
the common quantitative step after a finite-rank approximation correction.
-/

noncomputable section
open scoped ENNReal NNReal

namespace ComplementedSubspace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multipliers for a transported basis are exactly conjugate maps. -/
theorem basisMultiplier_map {n : ℕ} (b : Module.Basis (Fin n) ℝ E)
    (e : E ≃L[ℝ] F) (θ : Fin n → ℝ) :
    basisMultiplier (b.map e.toLinearEquiv) θ =
      e.toContinuousLinearMap.comp
        ((basisMultiplier b θ).comp e.symm.toContinuousLinearMap) := by
  apply ContinuousLinearMap.coe_injective
  apply (b.map e.toLinearEquiv).ext
  intro i
  change basisMultiplier (b.map e.toLinearEquiv) θ ((b.map e.toLinearEquiv) i) =
    e (basisMultiplier b θ (e.symm ((b.map e.toLinearEquiv) i)))
  rw [basisMultiplier_apply_basis]
  simp only [Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearEquiv.symm_apply_apply, basisMultiplier_apply_basis, map_smul]

/-- Pointwise bounds for both directions of an equivalence control every
transported multiplier. -/
theorem norm_basisMultiplier_map_apply_le {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) (e : E ≃L[ℝ] F)
    (A B C : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    (he : ∀ x, ‖e x‖ ≤ (A : ℝ) * ‖x‖)
    (hi : ∀ y, ‖e.symm y‖ ≤ (B : ℝ) * ‖y‖)
    (θ : Fin n → ℝ) (hθ : ∀ i, ‖θ i‖ ≤ 1) (y : F) :
    ‖basisMultiplier (b.map e.toLinearEquiv) θ y‖ ≤
      ((A * C * B : ℝ≥0) : ℝ) * ‖y‖ := by
  rw [basisMultiplier_map]
  change ‖e (basisMultiplier b θ (e.symm y))‖ ≤ _
  calc
    ‖e (basisMultiplier b θ (e.symm y))‖ ≤
        (A : ℝ) * ‖basisMultiplier b θ (e.symm y)‖ := he _
    _ ≤ (A : ℝ) * ((C : ℝ) * ‖e.symm y‖) :=
      mul_le_mul_of_nonneg_left
        (norm_basisMultiplier_le_bound b C hb ⟨θ, hθ⟩ _) A.2
    _ ≤ (A : ℝ) * ((C : ℝ) * ((B : ℝ) * ‖y‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hi y) C.2) A.2
    _ = _ := by simp only [NNReal.coe_mul, mul_assoc]

/-- Quantitative basis transport; the maximum also covers the zero space. -/
theorem unconditionalBasisConstant_map_le {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) (e : E ≃L[ℝ] F)
    (A B C : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    (he : ∀ x, ‖e x‖ ≤ (A : ℝ) * ‖x‖)
    (hi : ∀ y, ‖e.symm y‖ ≤ (B : ℝ) * ‖y‖) :
    unconditionalBasisConstant (b.map e.toLinearEquiv) ≤
      max 1 ((A * C * B : ℝ≥0) : ℝ≥0∞) := by
  apply max_le (le_max_left _ _)
  refine iSup_le fun θ => iSup_le fun hθ => ?_
  apply le_trans _ (le_max_right _ _)
  apply enorm_le_coe.mpr
  apply NNReal.coe_le_coe.mp
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_basisMultiplier_map_apply_le b e A B C hb he hi θ hθ

end ComplementedSubspace
