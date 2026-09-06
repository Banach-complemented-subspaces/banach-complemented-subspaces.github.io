import ComplementedSubspace.SelectedProjectionSetup
import ComplementedSubspace.FiniteOverlapMatrixNorms

/-! Normalize the actual selected basis and control its coefficient norm. -/
noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (F : Submodule ℝ (WithLp 2 (FrameCoefficient n p × H)))

def selectedFrameNormalizedBasis {r : ℕ} (b : Module.Basis (Fin r) ℝ F) :
    Module.Basis (Fin r) ℝ F :=
  hilbertNormalizedBasis (E := F)
    (H := selectedCoefficientHilbertSpace (frameCoefficientHilbertEquiv n p) F)
    b (selectedCoefficientHilbertEquiv (frameCoefficientHilbertEquiv n p) F)

theorem selectedFrameNormalizedBasis_constant {r : ℕ} (b : Module.Basis (Fin r) ℝ F) :
    unconditionalBasisConstant (selectedFrameNormalizedBasis F b) = unconditionalBasisConstant b :=
  hilbertNormalizedBasis_constant (E := F)
    (H := selectedCoefficientHilbertSpace (frameCoefficientHilbertEquiv n p) F) b _

theorem selectedFrameNormalizedBasis_norm {r : ℕ} (b : Module.Basis (Fin r) ℝ F) (i : Fin r) :
    ‖selectedCoefficientHilbertEquiv (frameCoefficientHilbertEquiv n p) F
      (selectedFrameNormalizedBasis F b i)‖ = 1 :=
  hilbertNormalizedBasis_norm (E := F)
    (H := selectedCoefficientHilbertSpace (frameCoefficientHilbertEquiv n p) F) b _ i

variable [FiniteDimensional ℝ F]

theorem selectedCoefficient_euclidean_norm_le (z : F) :
    ‖WithLp.toLp 2 (fun k => selectedProductFst F z k)‖ ≤
      ‖selectedCoefficientHilbertEquiv (frameCoefficientHilbertEquiv n p) F z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  exact selectedCoefficient_coordinate_sq_le F z

end ComplementedSubspace

