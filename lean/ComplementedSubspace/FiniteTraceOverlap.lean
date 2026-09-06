import ComplementedSubspace.ProductFrameTraceBound
import ComplementedSubspace.FiniteHilbertAverage
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Retained trace forces a quantitative Hilbert overlap -/

noncomputable section
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

def frameCoefficientStandardBasis (n : ℕ) (p : ℝ) :
    Module.Basis (MomentIndex n) ℝ (FrameCoefficient n p) :=
  Pi.basisFun ℝ (MomentIndex n)

theorem frameCoefficient_trace_eq_basis_sum (n : ℕ) (p : ℝ)
    (A : FrameCoefficient n p →ₗ[ℝ] FrameCoefficient n p) :
    LinearMap.trace ℝ (FrameCoefficient n p) A =
      ∑ i, A (Pi.single i 1) i := by
  exact frameCoefficient_trace_eq_sum n p A

theorem frameCoefficient_hilbert_sign_energy (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A : FrameCoefficient n p →L[ℝ] G) :
    (∑ i, ‖A (Pi.single i 1)‖ ^ 2) =
      (2 : ℝ) ^ n * finiteAverage (fun s => ‖A (frameCoefficientSignSample n p s)‖ ^ 2) := by
  let L : (MomentIndex n → ℝ) →ₗ[ℝ] G := A.toLinearMap
  have h := finiteAverage_linearMap_norm_sq (normalizedFrameSign n) L
  simp only [normalizedFrameSign_covariance, ite_div, zero_div,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    real_inner_self_eq_norm_sq, one_div, ← Finset.sum_mul] at h
  have h' : finiteAverage (fun s => ‖A (frameCoefficientSignSample n p s)‖ ^ 2) =
      (∑ i, ‖A (Pi.single i 1)‖ ^ 2) * ((2 : ℝ) ^ n)⁻¹ := by
    exact h
  rw [h']
  have hq : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

theorem frameCoefficient_hilbert_energy_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A : FrameCoefficient n p →L[ℝ] G) :
    (∑ i, ‖A (Pi.single i 1)‖ ^ 2) ≤
      (2 : ℝ) ^ n * realFrameSignConstant p ^ 2 * ‖A‖ ^ 2 := by
  rw [frameCoefficient_hilbert_sign_energy]
  have hmean : finiteAverage (fun s => ‖A (frameCoefficientSignSample n p s)‖ ^ 2) ≤
      ‖A‖ ^ 2 * realFrameSignConstant p ^ 2 := by
    calc
      _ ≤ finiteAverage (fun s => ‖A‖ ^ 2 * ‖frameCoefficientSignSample n p s‖ ^ 2) := by
        apply finiteAverage_mono
        intro s
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
          (A.le_opNorm (frameCoefficientSignSample n p s)) 2
      _ = ‖A‖ ^ 2 * finiteAverage (fun s => ‖frameCoefficientSignSample n p s‖ ^ 2) :=
        finiteAverage_mul _ _
      _ ≤ _ := by
        rw [realFrameSignConstant_sq]
        exact mul_le_mul_of_nonneg_left
          (frameCoefficientSignSample_norm_sq_average_le n p hp₂ hp₄) (sq_nonneg _)
  calc
    _ ≤ (2 : ℝ) ^ n * (‖A‖ ^ 2 * realFrameSignConstant p ^ 2) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by ring

theorem frame_trace_pairing_sq_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A : FrameCoefficient n p →L[ℝ] F) (B : F →L[ℝ] FrameCoefficient n p)
    (T : F →L[ℝ] G) (v : MomentIndex n → G)
    (hcoord : ∀ z i, B z i = inner ℝ (T z) (v i)) :
    (LinearMap.trace ℝ (FrameCoefficient n p) (B.comp A).toLinearMap) ^ 2 ≤
      (∑ i, ‖T (A (Pi.single i 1))‖ ^ 2) *
        (∑ i, ‖v i‖ ^ 2) := by
  rw [frameCoefficient_trace_eq_basis_sum]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, hcoord]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    _ (fun i _ => sq_nonneg _) (fun i _ => sq_nonneg _)
  intro i _
  have h := norm_inner_le_norm (𝕜 := ℝ) (T (A (Pi.single i 1))) (v i)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using hs

/-- The coefficient functionals may be represented by orthogonal-projection
columns. A retained half trace then forces nonvanishing normalized overlap. -/
theorem frame_trace_forces_overlap (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A : FrameCoefficient n p →L[ℝ] F) (B : F →L[ℝ] FrameCoefficient n p)
    (T : F →L[ℝ] G) (v : MomentIndex n → G)
    (hcoord : ∀ z i, B z i = inner ℝ (T z) (v i))
    (hT : ∀ z, ‖T z‖ ≤ ‖z‖) {K : ℝ} (hK : 0 ≤ K) (hA : ‖A‖ ≤ K)
    (htrace : (2 : ℝ) ^ n / 2 ≤
      LinearMap.trace ℝ (FrameCoefficient n p) (B.comp A).toLinearMap) :
    1 ≤ 4 * K ^ 2 * realFrameSignConstant p ^ 2 *
      (((2 : ℝ) ^ n)⁻¹ * ∑ i, ‖v i‖ ^ 2) := by
  have hTA : ‖T.comp A‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro x
    exact (hT _).trans ((A.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg x)))
  have henergy := frameCoefficient_hilbert_energy_le n p hp₂ hp₄ (T.comp A)
  have hpair := frame_trace_pairing_sq_le n p A B T v hcoord
  have hq : 0 < (2 : ℝ) ^ n := by positivity
  have hv : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq := pow_le_pow_left₀ (norm_nonneg (T.comp A)) hTA 2
  have henergy' : (∑ i, ‖T (A (Pi.single i 1))‖ ^ 2) ≤
      (2 : ℝ) ^ n * realFrameSignConstant p ^ 2 * K ^ 2 := by
    exact henergy.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  have hpair' := hpair.trans (mul_le_mul_of_nonneg_right henergy' hv)
  have htrsq := pow_le_pow_left₀ (div_nonneg hq.le (by norm_num)) htrace 2
  have hbound : (2 : ℝ) ^ n ≤ 4 * realFrameSignConstant p ^ 2 * K ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
    have hm : (2 : ℝ) ^ n * (2 : ℝ) ^ n ≤
        (2 : ℝ) ^ n * (4 * realFrameSignConstant p ^ 2 * K ^ 2 * ∑ i, ‖v i‖ ^ 2) := by
      nlinarith [htrsq.trans hpair']
    exact le_of_mul_le_mul_left hm hq
  have h := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hq.le)
  rw [inv_mul_cancel₀ hq.ne'] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end ComplementedSubspace
