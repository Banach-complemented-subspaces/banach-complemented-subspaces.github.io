import ComplementedSubspace.FiniteProductObstruction
import ComplementedSubspace.FiniteDualSuperspace
import ComplementedSubspace.FiniteOverlapDualScale
import ComplementedSubspace.DPRObstruction
import ComplementedSubspace.LocalHilbertTransport

/-! DPR lower bounds with explicit scalar hypotheses, including doubled head bounds. -/

noncomputable section
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

variable {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem frame_product_le_chiDPR_of_bounds {n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (e : Z ≃ₗᵢ[ℝ] WithLp 2 (FrameCoefficient n p × W))
    (D K : ℝ≥0) (hD : 1 ≤ D) (hK : 1 ≤ K)
    (hlocal : LocallyHilbertWithin W (3 * 2 ^ n) D)
    (hsmall : (((2 : ℝ) ^ n * realFrameSignConstant p / realFrameWitnessScale n p) *
      (D : ℝ) * (K : ℝ) ^ 2) ≤ (2 : ℝ) ^ n / 4)
    (hsep : 256 * (K : ℝ) ^ 2 * realFrameSignConstant p ^ 2 * ((D : ℝ) * (K : ℝ)) ^ 3 <
      realFrameOverlapScale n p) : (K : ℝ≥0∞) ≤ chiDPR Z := by
  letI : Nontrivial (FrameCoefficient n p) := Module.nontrivial_of_finrank_pos (by
    rw [frameCoefficient_finrank]
    positivity)
  let I := IsometricProductSplitting.inclusion e
  let R := IsometricProductSplitting.first e
  let J := IsometricProductSplitting.tailInclusion e
  let S := IsometricProductSplitting.second e
  apply le_chiDPR_of_basis_obstruction K I.range inferInstance
    (isometricProduct_first_range_ne_bot e)
  intro F hIF _ m b
  apply le_of_lt
  apply lt_of_not_ge
  intro hb
  let eF := SuperspaceSplitting.equiv F I R J S hIF
    (IsometricProductSplitting.first_inclusion e) (IsometricProductSplitting.tail_second e)
    (IsometricProductSplitting.first_tailInclusion e) (IsometricProductSplitting.second_tailInclusion e)
    (IsometricProductSplitting.inclusion_contracts e) (IsometricProductSplitting.norm_sq e)
  apply finite_basis_obstruction_of_frame_product hp₂ hp₃ b eF D K hD hK hb _ hsmall hsep
  intro V _ hV
  exact localHilbert_subspace hlocal (F.map S.toLinearMap) V hV

theorem frame_product_le_chiDPR_with_doubled_head {n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (e : Z ≃ₗᵢ[ℝ] WithLp 2 (FrameCoefficient n p × W))
    (D K : ℝ≥0) (hD : 2 ≤ D) (hK : 1 ≤ K)
    (hlocal : LocallyHilbertWithin W (3 * 2 ^ n) (2 * (D : ℝ)))
    (hDK : 16 * K ≤ D) (hL : (D : ℝ) ^ 8 < realFrameOverlapScale n p) :
    (K : ℝ≥0∞) ≤ chiDPR Z := by
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hDKr : 16 * (K : ℝ) ≤ D := by exact_mod_cast hDK
  obtain ⟨hsmall, hsep⟩ := finite_frame_dual_selection_scalar_bounds n p D K
    hp₂ hp₃ hDr K.2 hDKr hL
  have h2D : (1 : ℝ≥0) ≤ 2 * D := by
    exact_mod_cast (show (1 : ℝ) ≤ 2 * (D : ℝ) by linarith)
  exact frame_product_le_chiDPR_of_bounds hp₂ hp₃ e (2 * D) K h2D hK
    (by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hlocal)
    (by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hsmall)
    (by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hsep)

end ComplementedSubspace
