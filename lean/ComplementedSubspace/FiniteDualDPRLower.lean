import ComplementedSubspace.FiniteProductObstruction
import ComplementedSubspace.FiniteOverlapDualScale
import ComplementedSubspace.FiniteDualBasis
import ComplementedSubspace.FiniteDualSuperspace
import ComplementedSubspace.DPRObstruction

/-! The finite-superspace dual argument uses the actual continuous dual twice. -/

noncomputable section
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

variable {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem frame_product_le_chiDPR_dual {n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (eZ : Z ≃ₗᵢ[ℝ] WithLp 2 (FrameCoefficient n p × W))
    (D K : ℝ≥0) (hD : 2 ≤ D) (hK : 1 ≤ K)
    (hlocal : DualSubspacesLocallyHilbertWithin (StrongDual ℝ W) (3 * 2 ^ n) (2 * (D : ℝ)))
    (hDK : 16 * K ≤ D) (hL : (D : ℝ) ^ 8 < realFrameOverlapScale n p) :
    (K : ℝ≥0∞) ≤ chiDPR (StrongDual ℝ Z) := by
  let e : StrongDual ℝ Z ≃ₗᵢ[ℝ]
      WithLp 2 (StrongDual ℝ (FrameCoefficient n p) × StrongDual ℝ W) :=
    (realDualIsometryEquiv eZ).trans (prodL2DualEquiv (FrameCoefficient n p) W)
  let I : StrongDual ℝ (FrameCoefficient n p) →L[ℝ] StrongDual ℝ Z :=
    IsometricProductSplitting.inclusion e
  let S : StrongDual ℝ Z →L[ℝ] StrongDual ℝ W := IsometricProductSplitting.second e
  letI : Nontrivial (StrongDual ℝ (FrameCoefficient n p)) := Module.nontrivial_of_finrank_pos (by
    rw [finiteStrongDual_finrank, frameCoefficient_finrank]
    positivity)
  have hIrange : I.range ≠ ⊥ := isometricProduct_first_range_ne_bot e
  apply le_chiDPR_of_basis_obstruction K I.range inferInstance hIrange
  intro F hIF _ m b
  apply le_of_lt
  apply lt_of_not_ge
  intro hb
  let V : Submodule ℝ (StrongDual ℝ W) := F.map S.toLinearMap
  letI : NormedAddCommGroup V := inferInstance
  letI : NormedSpace ℝ V := inferInstance
  let eFD' : StrongDual ℝ F ≃ₗᵢ[ℝ]
      WithLp 2 (FrameCoefficient n p × StrongDual ℝ V) :=
    finiteSuperspaceDualProductEquiv (E := FrameCoefficient n p)
      (W := StrongDual ℝ W) (Z := StrongDual ℝ Z) e F hIF
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hDKr : 16 * (K : ℝ) ≤ D := by exact_mod_cast hDK
  obtain ⟨hsmall, hsep⟩ := finite_frame_dual_selection_scalar_bounds n p D K
    hp₂ hp₃ hDr K.2 hDKr hL
  apply @finite_basis_obstruction_of_frame_product
    (StrongDual ℝ F) (StrongDual ℝ V)
    (inferInstance : NormedAddCommGroup (StrongDual ℝ F))
    (inferInstance : NormedSpace ℝ (StrongDual ℝ F))
    (inferInstance : NormedAddCommGroup (StrongDual ℝ V))
    (inferInstance : NormedSpace ℝ (StrongDual ℝ V))
    m n p inferInstance
    hp₂ hp₃ (continuousDualBasis b)
    eFD' (2 * D) K _ hK ((continuousDualBasis_constant_le b).trans hb) _
    (by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hsmall)
    (by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hsep)
  · exact_mod_cast (show (1 : ℝ) ≤ 2 * (D : ℝ) by linarith)
  · intro U _ hU
    change HasHilbertNormWithin U (2 * (D : ℝ))
    exact hlocal V U hU

end ComplementedSubspace
