import ComplementedSubspace.IsometricProductDPRLower
import ComplementedSubspace.LocalHilbertDualTop

/-! A bidual DPR obstruction from the same geometry used for the dual. -/

noncomputable section
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

variable {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem frame_product_le_chiDPR_bidual {n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (eZ : Z ≃ₗᵢ[ℝ] WithLp 2 (FrameCoefficient n p × W))
    (D K : ℝ≥0) (hD : 2 ≤ D) (hK : 1 ≤ K)
    (hlocal : DualSubspacesLocallyHilbertWithin (StrongDual ℝ W) (3 * 2 ^ n) (2 * (D : ℝ)))
    (hDK : 16 * K ≤ D) (hL : (D : ℝ) ^ 8 < realFrameOverlapScale n p) :
    (K : ℝ≥0∞) ≤ chiDPR (StrongDual ℝ (StrongDual ℝ Z)) := by
  let eDD : StrongDual ℝ (StrongDual ℝ Z) ≃ₗᵢ[ℝ]
      WithLp 2 (FrameCoefficient n p × StrongDual ℝ (StrongDual ℝ W)) :=
    ((realDualIsometryEquiv (realDualIsometryEquiv eZ)).trans
    (prodL2BidualEquiv (FrameCoefficient n p) W)).trans
    ((finiteBidualEquiv (FrameCoefficient n p)).symm.withLpProdCongr 2
      (LinearIsometryEquiv.refl ℝ (StrongDual ℝ (StrongDual ℝ W))))
  exact frame_product_le_chiDPR_with_doubled_head hp₂ hp₃ eDD D K hD hK
    (locallyHilbert_bidual_of_dualSubspaces hlocal) hDK hL

end ComplementedSubspace
