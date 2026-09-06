import ComplementedSubspace.SelectedCoefficientHilbert
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Concrete coordinate maps and orthogonal projection for a selected subspace. -/
noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

section General
variable {E E₂ H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def hilbertFirstInclusion (E₂ H : Type*) [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] : E₂ →L[ℝ] WithLp 2 (E₂ × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E₂ H).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ E₂).prod (0 : E₂ →L[ℝ] H))

@[simp] theorem hilbertFirstInclusion_fst (x : E₂) :
    (hilbertFirstInclusion E₂ H x).fst = x := rfl

@[simp] theorem hilbertFirstInclusion_snd (x : E₂) :
    (hilbertFirstInclusion E₂ H x).snd = 0 := rfl

@[simp] theorem hilbertFirstInclusion_norm (x : E₂) :
    ‖hilbertFirstInclusion E₂ H x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [WithLp.prod_norm_sq_eq_of_L2]

def selectedProductFst (F : Submodule ℝ (WithLp 2 (E × H))) : F →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E H).comp F.subtypeL

def selectedProductSnd (F : Submodule ℝ (WithLp 2 (E × H))) : F →L[ℝ] H :=
  (WithLp.sndL 2 ℝ E H).comp F.subtypeL

@[simp] theorem selectedProductFst_apply (F : Submodule ℝ (WithLp 2 (E × H))) (z : F) :
    selectedProductFst F z = (z : WithLp 2 (E × H)).fst := rfl

@[simp] theorem selectedProductSnd_apply (F : Submodule ℝ (WithLp 2 (E × H))) (z : F) :
    selectedProductSnd F z = (z : WithLp 2 (E × H)).snd := rfl

theorem selectedProduct_norm_sq (F : Submodule ℝ (WithLp 2 (E × H))) (z : F) :
    ‖z‖ ^ 2 = ‖selectedProductFst F z‖ ^ 2 + ‖selectedProductSnd F z‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (z : WithLp 2 (E × H))

theorem selectedProductFst_contracts (F : Submodule ℝ (WithLp 2 (E × H))) (z : F) :
    ‖selectedProductFst F z‖ ≤ ‖z‖ :=
  WithLp.norm_fst_le (p := 2) (β := H) E (z : WithLp 2 (E × H))

theorem selectedProductSnd_contracts (F : Submodule ℝ (WithLp 2 (E × H))) (z : F) :
    ‖selectedProductSnd F z‖ ≤ ‖z‖ :=
  WithLp.norm_snd_le (p := 2) (β := H) E (z : WithLp 2 (E × H))

variable (e : E ≃L[ℝ] E₂) (F : Submodule ℝ (WithLp 2 (E × H)))
  [FiniteDimensional ℝ F]

instance selectedCoefficientHilbertSpace_finiteDimensional :
    FiniteDimensional ℝ (selectedCoefficientHilbertSpace e F) :=
  (selectedCoefficientHilbertEquiv e F).toLinearEquiv.finiteDimensional

theorem selectedCoefficientHilbertEquiv_norm_le_one (hlo : ∀ x, ‖e x‖ ≤ ‖x‖) :
    ‖(selectedCoefficientHilbertEquiv e F).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖selectedCoefficientHilbertEquiv e F z‖ ≤ 1 * ‖z‖
  rw [one_mul]
  exact selectedCoefficientHilbertEquiv_contracts e F hlo z

/-- Project in the Hilbert product and return to the original selected norm. -/
def selectedOrthogonalLift : E₂ →L[ℝ] F :=
  (selectedCoefficientHilbertEquiv e F).symm.toContinuousLinearMap.comp
    ((selectedCoefficientHilbertSpace e F).orthogonalProjectionOnto.comp
      (hilbertFirstInclusion E₂ H))

@[simp] theorem selectedOrthogonalLift_image (x : E₂) :
    selectedCoefficientHilbertEquiv e F (selectedOrthogonalLift e F x) =
      (selectedCoefficientHilbertSpace e F).orthogonalProjectionOnto (hilbertFirstInclusion E₂ H x) :=
  (selectedCoefficientHilbertEquiv e F).apply_symm_apply _

theorem selectedOrthogonalLift_image_contracts (x : E₂) :
    ‖selectedCoefficientHilbertEquiv e F (selectedOrthogonalLift e F x)‖ ≤ ‖x‖ := by
  rw [selectedOrthogonalLift_image]
  simpa only [hilbertFirstInclusion_norm] using
    (selectedCoefficientHilbertSpace e F).norm_orthogonalProjectionOnto_apply_le
      (hilbertFirstInclusion E₂ H x)

theorem selectedOrthogonalLift_snd_eq (x : E₂) :
    selectedProductSnd F (selectedOrthogonalLift e F x) =
      ((selectedCoefficientHilbertSpace e F).orthogonalProjectionOnto
        (hilbertFirstInclusion E₂ H x) : WithLp 2 (E₂ × H)).snd := by
  rw [← selectedOrthogonalLift_image]
  rfl

theorem selectedOrthogonalLift_snd_norm_le :
    ‖(selectedProductSnd F).comp (selectedOrthogonalLift e F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖selectedProductSnd F (selectedOrthogonalLift e F x)‖ ≤ 1 * ‖x‖
  rw [selectedOrthogonalLift_snd_eq, one_mul]
  exact (WithLp.norm_snd_le (p := 2) (β := H) E₂ _).trans
    ((selectedCoefficientHilbertSpace e F).norm_orthogonalProjectionOnto_apply_le _ |>.trans
      (hilbertFirstInclusion_norm (H := H) x).le)

def selectedOrthogonalFirstOperator : E₂ →L[ℝ] E₂ :=
  (WithLp.fstL 2 ℝ E₂ H).comp
    ((selectedCoefficientHilbertSpace e F).subtypeL.comp
      ((selectedCoefficientHilbertSpace e F).orthogonalProjectionOnto.comp
        (hilbertFirstInclusion E₂ H)))

theorem selectedOrthogonalFirstOperator_norm_le : ‖selectedOrthogonalFirstOperator e F‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖((selectedCoefficientHilbertSpace e F).orthogonalProjectionOnto
    (hilbertFirstInclusion E₂ H x) : WithLp 2 (E₂ × H)).fst‖ ≤ 1 * ‖x‖
  rw [one_mul]
  exact (WithLp.norm_fst_le (p := 2) (β := H) E₂ _).trans
    ((selectedCoefficientHilbertSpace e F).norm_orthogonalProjectionOnto_apply_le _ |>.trans
      (hilbertFirstInclusion_norm (H := H) x).le)

theorem selectedOrthogonalFirstOperator_eq (x : E₂) :
    selectedOrthogonalFirstOperator e F x = e (selectedProductFst F (selectedOrthogonalLift e F x)) := by
  change ((selectedCoefficientHilbertSpace e F).orthogonalProjectionOnto
    (hilbertFirstInclusion E₂ H x) : WithLp 2 (E₂ × H)).fst = _
  rw [← selectedOrthogonalLift_image]
  rfl

end General

section Frame
variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (F : Submodule ℝ (WithLp 2 (FrameCoefficient n p × H))) [FiniteDimensional ℝ F]

def selectedOrthogonalCoefficientMatrix : Matrix (MomentIndex n) (MomentIndex n) ℝ :=
  Matrix.toEuclideanLin.symm
    (selectedOrthogonalFirstOperator (frameCoefficientHilbertEquiv n p) F).toLinearMap

theorem selectedOrthogonalCoefficientMatrix_operator :
    Matrix.toEuclideanLin (selectedOrthogonalCoefficientMatrix F) =
      (selectedOrthogonalFirstOperator (frameCoefficientHilbertEquiv n p) F).toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

theorem selectedOrthogonalCoefficientMatrix_norm_le : ‖selectedOrthogonalCoefficientMatrix F‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  change ‖(Matrix.toEuclideanLin (selectedOrthogonalCoefficientMatrix F)).toContinuousLinearMap‖ ≤ 1
  rw [selectedOrthogonalCoefficientMatrix_operator]
  exact selectedOrthogonalFirstOperator_norm_le (frameCoefficientHilbertEquiv n p) F

theorem selectedOrthogonalCoefficientMatrix_mulVec (x : MomentIndex n → ℝ) :
    selectedProductFst F (selectedOrthogonalLift (frameCoefficientHilbertEquiv n p) F (WithLp.toLp 2 x)) =
      (selectedOrthogonalCoefficientMatrix F).mulVec x := by
  have h := congrArg (fun L : EuclideanSpace ℝ (MomentIndex n) →ₗ[ℝ]
    EuclideanSpace ℝ (MomentIndex n) => L (WithLp.toLp 2 x))
    (selectedOrthogonalCoefficientMatrix_operator F)
  rw [Matrix.toLpLin_apply] at h
  change WithLp.toLp 2 ((selectedOrthogonalCoefficientMatrix F).mulVec x) =
    selectedOrthogonalFirstOperator (frameCoefficientHilbertEquiv n p) F (WithLp.toLp 2 x) at h
  rw [selectedOrthogonalFirstOperator_eq] at h
  exact congrArg WithLp.ofLp h.symm

theorem selectedCoefficient_coordinate_sq_le (z : F) :
    (∑ i, (selectedProductFst F z i) ^ 2) ≤
      ‖selectedCoefficientHilbertEquiv (frameCoefficientHilbertEquiv n p) F z‖ ^ 2 := by
  change (∑ i, (selectedProductFst F z i) ^ 2) ≤
    ‖hilbertCoefficientProductEquiv (H := H) (frameCoefficientHilbertEquiv n p)
      (z : WithLp 2 (FrameCoefficient n p × H))‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2, hilbertCoefficientProductEquiv_fst,
    hilbertCoefficientProductEquiv_snd, frameCoefficientHilbertEquiv_norm_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem selectedCoefficientHilbert_first_pairing (z : F) (x : MomentIndex n → ℝ) :
    inner ℝ (selectedCoefficientHilbertEquiv (frameCoefficientHilbertEquiv n p) F z :
      WithLp 2 (EuclideanSpace ℝ (MomentIndex n) × H))
      (hilbertFirstInclusion (EuclideanSpace ℝ (MomentIndex n)) H (WithLp.toLp 2 x)) =
        ∑ i, selectedProductFst F z i * x i := by
  simp only [WithLp.prod_inner_apply, hilbertFirstInclusion, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
  change inner ℝ (frameCoefficientHilbertEquiv n p (selectedProductFst F z))
    (WithLp.toLp 2 x) + inner ℝ (selectedProductSnd F z) 0 = _
  rw [inner_zero_right, add_zero]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    frameCoefficientHilbertEquiv_apply, WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Frame
end ComplementedSubspace
