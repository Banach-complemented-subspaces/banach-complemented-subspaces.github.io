import ComplementedSubspace.FiniteBlockObstruction
import ComplementedSubspace.IsometricProductSplitting

/-! Applying the finite frame obstruction through an actual product isometry. -/

noncomputable section
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {Y W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem finite_basis_obstruction_of_frame_product {m n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (b : Module.Basis (Fin m) ℝ Y)
    (e : Y ≃ₗᵢ[ℝ] WithLp 2 (FrameCoefficient n p × W))
    (D K : ℝ≥0) (hD : 1 ≤ D) (hK : 1 ≤ K)
    (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    (hlocal : ∀ (V : Submodule ℝ W) [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ 3 * 2 ^ n → HasHilbertNormWithin V D)
    (hsmall : (((2 : ℝ) ^ n * realFrameSignConstant p / realFrameWitnessScale n p) *
      (D : ℝ) * (K : ℝ) ^ 2) ≤ (2 : ℝ) ^ n / 4)
    (hsep : 256 * (K : ℝ) ^ 2 * realFrameSignConstant p ^ 2 * ((D : ℝ) * (K : ℝ)) ^ 3 <
      realFrameOverlapScale n p) : False := by
  exact finite_basis_obstruction_with_frame_summand hp₂ hp₃ b
    (IsometricProductSplitting.inclusion e) (IsometricProductSplitting.first e)
    (IsometricProductSplitting.tailInclusion e) (IsometricProductSplitting.second e)
    (IsometricProductSplitting.first_inclusion e) (IsometricProductSplitting.tail_second e)
    (IsometricProductSplitting.norm_sq e) (IsometricProductSplitting.inclusion_contracts e)
    (IsometricProductSplitting.first_contracts e) (IsometricProductSplitting.tailInclusion_contracts e)
    (IsometricProductSplitting.second_contracts e) D K hD hK hb hlocal hsmall hsep

end ComplementedSubspace
