import ComplementedSubspace.FiniteOverlapConclusion
import ComplementedSubspace.SelectedProjectionSetup
import ComplementedSubspace.ProjectionOverlapLower

/-! The finite obstruction for an actual selected subspace of E ⊕₂ H. -/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256
open scoped Matrix.Norms.L2Operator ENNReal NNReal BigOperators
namespace ComplementedSubspace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The overlap upper bound for an actual small subspace. All component maps,
orthogonal projections, matrix contractions, and basis normalization are
constructed here from the given subspace and its unconditional basis. -/
theorem finite_selected_projection_overlap_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (F : Submodule ℝ (WithLp 2 (FrameCoefficient n p × H)))
    [FiniteDimensional ℝ F] {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (C : ℝ≥0) (hC : 1 ≤ (C : ℝ))
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    (hm : (m : ℝ) ≤ 3 * (2 : ℝ) ^ n) :
    frameProjectionOverlap n
      (hilbertFirstInclusion (EuclideanSpace ℝ (MomentIndex n)) H)
      (selectedCoefficientHilbertSpace (frameCoefficientHilbertEquiv n p) F) ≤
      64 * (C : ℝ) ^ 3 / realFrameOverlapScale n p := by
  let e₀ := frameCoefficientHilbertEquiv n p
  let T := selectedCoefficientHilbertEquiv e₀ F
  let P := selectedOrthogonalLift e₀ F
  obtain ⟨c, hconstant, hnormal⟩ := exists_hilbert_normalized_basis
    (E := F) (H := selectedCoefficientHilbertSpace e₀ F) b T
  have hc : unconditionalBasisConstant c ≤ (C : ℝ≥0∞) := hconstant.le.trans hb
  have hlo : ∀ z, ‖T z‖ ≤ ‖z‖ := fun z =>
    (frameSelectedCoefficientHilbert_bounds hp₂ F z).1
  have hhi : ∀ z, ‖z‖ ≤ realFrameHilbertScale n p * ‖T z‖ := fun z =>
    (frameSelectedCoefficientHilbert_bounds hp₂ F z).2
  have heH : ∀ z, ‖WithLp.toLp 2 (fun k => selectedProductFst F z k)‖ ≤ ‖T z‖ := by
    intro z
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply] using
      selectedCoefficient_coordinate_sq_le F z
  have hP : ∀ x, ‖T (P x)‖ ≤ ‖x‖ := selectedOrthogonalLift_image_contracts e₀ F
  have hnorm : ∀ z : F, ‖z‖ ^ 2 =
      ‖selectedProductFst F z‖ ^ 2 + ‖selectedProductSnd F z‖ ^ 2 := selectedProduct_norm_sq F
  let R := selectedOrthogonalCoefficientMatrix F
  have hR : ‖R‖ ≤ 1 := selectedOrthogonalCoefficientMatrix_norm_le F
  have he : ∀ x : MomentIndex n → ℝ,
      selectedProductFst F (P (WithLp.toLp 2 x)) = R.mulVec x :=
    selectedOrthogonalCoefficientMatrix_mulVec F
  have hh : ‖(selectedProductSnd F).comp P‖ ≤ 1 := selectedOrthogonalLift_snd_norm_le e₀ F
  -- Explicit instances avoid repeatedly unfolding the two normed-space paths
  -- on the concrete selected Hilbert subtype during specialization.
  have hupper : realFrameWitnessScale n (frameConjugate p) *
      finiteAverage (fun x => ‖P (overlapInputRow n x)‖) ≤
      64 * (C : ℝ) ^ 3 / realFrameOverlapScale n p := @finite_basis_overlap_scaled_bound
    F (selectedCoefficientHilbertSpace e₀ F) H
    (inferInstance : NormedAddCommGroup F) (inferInstance : NormedSpace ℝ F)
    (inferInstance : NormedAddCommGroup (selectedCoefficientHilbertSpace e₀ F))
    (inferInstance : InnerProductSpace ℝ (selectedCoefficientHilbertSpace e₀ F))
    (inferInstance : NormedAddCommGroup H) (inferInstance : InnerProductSpace ℝ H)
    n p inferInstance hp₂ hp₃ m c T P
    (selectedProductFst F) (selectedProductSnd F) C hC hc hm hlo hhi
    hnormal heH hP hnorm R hR he hh
  have hlower := frame_projection_overlap_mean_lower n p (by linarith)
    (selectedCoefficientHilbertSpace e₀ F)
    (hilbertFirstInclusion (EuclideanSpace ℝ (MomentIndex n)) H)
    T (selectedProductFst F) (selectedProductFst_contracts F)
    (selectedCoefficientHilbert_first_pairing F)
  have hrow (s : FrameIndex n) :
      T.symm ((selectedCoefficientHilbertSpace e₀ F).orthogonalProjectionOnto
        (hilbertFirstInclusion (EuclideanSpace ℝ (MomentIndex n)) H
          (WithLp.toLp 2 (normalizedProductFrameRow n s)))) = P (overlapInputRow n s) := by
    rfl
  simp_rw [hrow] at hlower
  exact hlower.trans hupper

/-- Retained trace through an actual small unconditional subspace forces a
quantitative upper bound on the finite-frame overlap separation scale. -/
theorem finite_selected_trace_scale_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (F : Submodule ℝ (WithLp 2 (FrameCoefficient n p × H)))
    [FiniteDimensional ℝ F] {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (C : ℝ≥0) (hC : 1 ≤ (C : ℝ))
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    (hm : (m : ℝ) ≤ 3 * (2 : ℝ) ^ n)
    (A : FrameCoefficient n p →L[ℝ] F) {K : ℝ} (hK : 0 ≤ K)
    (hA : ‖A‖ ≤ K)
    (htrace : (2 : ℝ) ^ n / 2 ≤ LinearMap.trace ℝ (FrameCoefficient n p)
      ((selectedProductFst F).comp A).toLinearMap) :
    realFrameOverlapScale n p ≤ 256 * K ^ 2 * realFrameSignConstant p ^ 2 * (C : ℝ) ^ 3 := by
  let e₀ := frameCoefficientHilbertEquiv n p
  let T := selectedCoefficientHilbertEquiv e₀ F
  let S := selectedCoefficientHilbertSpace e₀ F
  let J := hilbertFirstInclusion (EuclideanSpace ℝ (MomentIndex n)) H
  have hcoord : ∀ z i, selectedProductFst F z i =
      inner ℝ (T z : WithLp 2 (EuclideanSpace ℝ (MomentIndex n) × H))
        (J (WithLp.toLp 2 (Pi.single i 1))) := by
    intro z i
    change selectedProductFst F z i = inner ℝ
      (selectedCoefficientHilbertEquiv (frameCoefficientHilbertEquiv n p) F z :
        WithLp 2 (EuclideanSpace ℝ (MomentIndex n) × H))
      (hilbertFirstInclusion (EuclideanSpace ℝ (MomentIndex n)) H
        (WithLp.toLp 2 (Pi.single i 1)))
    rw [selectedCoefficientHilbert_first_pairing]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hlo := frame_trace_forces_projection_overlap n p hp₂ (by linarith) S J
    A (selectedProductFst F) T.toContinuousLinearMap hcoord
    (fun z => (frameSelectedCoefficientHilbert_bounds hp₂ F z).1) hK hA htrace
  have hhi := finite_selected_projection_overlap_le n p hp₂ hp₃ F b C hC hb hm
  have hmul := mul_le_mul_of_nonneg_left hhi
    (show 0 ≤ 4 * K ^ 2 * realFrameSignConstant p ^ 2 by positivity)
  have hL : 0 < realFrameOverlapScale n p := Real.exp_pos _
  have hquot : 1 ≤ (256 * K ^ 2 * realFrameSignConstant p ^ 2 * (C : ℝ) ^ 3) /
      realFrameOverlapScale n p := by
    calc
      1 ≤ 4 * K ^ 2 * realFrameSignConstant p ^ 2 * frameProjectionOverlap n J S := hlo
      _ ≤ _ := hmul
      _ = _ := by ring
  simpa only [one_mul] using (le_div_iff₀ hL).mp hquot

theorem finite_selected_trace_obstruction (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (F : Submodule ℝ (WithLp 2 (FrameCoefficient n p × H)))
    [FiniteDimensional ℝ F] {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (C : ℝ≥0) (hC : 1 ≤ (C : ℝ))
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    (hm : (m : ℝ) ≤ 3 * (2 : ℝ) ^ n)
    (A : FrameCoefficient n p →L[ℝ] F) {K : ℝ} (hK : 0 ≤ K)
    (hA : ‖A‖ ≤ K)
    (htrace : (2 : ℝ) ^ n / 2 ≤ LinearMap.trace ℝ (FrameCoefficient n p)
      ((selectedProductFst F).comp A).toLinearMap)
    (hsep : 256 * K ^ 2 * realFrameSignConstant p ^ 2 * (C : ℝ) ^ 3 <
      realFrameOverlapScale n p) : False := by
  exact (not_lt_of_ge (finite_selected_trace_scale_le n p hp₂ hp₃ F b C hC hb hm
    A hK hA htrace)) hsep

end ComplementedSubspace
