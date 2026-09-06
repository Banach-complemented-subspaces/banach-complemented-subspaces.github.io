import ComplementedSubspace.FiniteTraceOverlap
import ComplementedSubspace.ProductFrameRowWitness

/-! # Lower overlap bounds for actual orthogonal projections -/

noncomputable section
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def frameProjectionOverlap (n : ℕ) (J : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] G)
    (S : Submodule ℝ G) [S.HasOrthogonalProjection] : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ i, ‖S.orthogonalProjectionOnto (J (WithLp.toLp 2 (Pi.single i 1)))‖ ^ 2

theorem frameProjectionOverlap_eq_row_average (n : ℕ)
    (J : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] G)
    (S : Submodule ℝ G) [S.HasOrthogonalProjection] :
    frameProjectionOverlap n J S = finiteAverage (fun s =>
      ‖S.orthogonalProjectionOnto (J (WithLp.toLp 2 (normalizedProductFrameRow n s)))‖ ^ 2) := by
  let A : (MomentIndex n → ℝ) →ₗ[ℝ] S :=
    S.orthogonalProjectionOnto.toLinearMap.comp
      (J.toLinearMap.comp (WithLp.linearEquiv 2 ℝ (MomentIndex n → ℝ)).symm.toLinearMap)
  have h := finiteAverage_linearMap_norm_sq (normalizedProductFrameRow n) A
  simp only [normalizedProductFrameRow_covariance, ite_div, zero_div,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    real_inner_self_eq_norm_sq, one_div, ← Finset.sum_mul] at h
  change ((2 : ℝ) ^ n)⁻¹ * (∑ i, ‖A (Pi.single i 1)‖ ^ 2) = _
  rw [mul_comm]
  exact h.symm

theorem frame_trace_forces_projection_overlap (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ G) [S.HasOrthogonalProjection]
    (J : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] G)
    (A : FrameCoefficient n p →L[ℝ] F) (B : F →L[ℝ] FrameCoefficient n p)
    (T : F →L[ℝ] S)
    (hcoord : ∀ z i, B z i = inner ℝ (T z : G) (J (WithLp.toLp 2 (Pi.single i 1))))
    (hT : ∀ z, ‖T z‖ ≤ ‖z‖) {K : ℝ} (hK : 0 ≤ K) (hA : ‖A‖ ≤ K)
    (htrace : (2 : ℝ) ^ n / 2 ≤
      LinearMap.trace ℝ (FrameCoefficient n p) (B.comp A).toLinearMap) :
    1 ≤ 4 * K ^ 2 * realFrameSignConstant p ^ 2 * frameProjectionOverlap n J S := by
  apply frame_trace_forces_overlap n p hp₂ hp₄ A B T
    (fun i => S.orthogonalProjectionOnto (J (WithLp.toLp 2 (Pi.single i 1))))
    _ hT hK hA htrace
  intro z i
  rw [S.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact hcoord z i

theorem frame_projection_overlap_mean_lower (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ G) [S.HasOrthogonalProjection]
    (J : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] G)
    (T : F ≃L[ℝ] S) (B : F →L[ℝ] FrameCoefficient n p)
    (hB : ∀ z, ‖B z‖ ≤ ‖z‖)
    (hpair : ∀ z (x : MomentIndex n → ℝ),
      inner ℝ (T z : G) (J (WithLp.toLp 2 x)) = ∑ i, B z i * x i) :
    frameProjectionOverlap n J S ≤ realFrameWitnessScale n (frameConjugate p) *
      finiteAverage (fun s =>
        ‖T.symm (S.orthogonalProjectionOnto (J (WithLp.toLp 2 (normalizedProductFrameRow n s))))‖) := by
  rw [frameProjectionOverlap_eq_row_average, ← finiteAverage_mul]
  apply finiteAverage_mono
  intro s
  let x := J (WithLp.toLp 2 (normalizedProductFrameRow n s))
  let z := S.orthogonalProjectionOnto x
  let y := T.symm z
  have hz : T y = z := T.apply_symm_apply z
  have hinner : ‖z‖ ^ 2 = inner ℝ (z : G) x := by
    rw [← real_inner_self_eq_norm_sq]
    exact S.inner_orthogonalProjectionOnto_eq_of_mem_left z x
  have heq : ‖z‖ ^ 2 = ∑ i, B y i * normalizedProductFrameRow n s i := by
    rw [hinner, ← hz]
    exact hpair y _
  change ‖z‖ ^ 2 ≤ realFrameWitnessScale n (frameConjugate p) * ‖y‖
  calc
    _ = |∑ i, B y i * normalizedProductFrameRow n s i| := by
      rw [← heq, abs_of_nonneg (sq_nonneg _)]
    _ ≤ realFrameWitnessScale n (frameConjugate p) * ‖B y‖ :=
      frameCoefficientRow_pairing_le n p s hp (B y)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB y) (Real.exp_pos _).le

end ComplementedSubspace
