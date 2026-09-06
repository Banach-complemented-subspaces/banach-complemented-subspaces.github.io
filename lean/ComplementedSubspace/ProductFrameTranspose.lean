import ComplementedSubspace.ProductFrameMoments

noncomputable section
namespace ComplementedSubspace
open Matrix

theorem productFrameFourth_swap_first (n : ℕ) (i j k l : MomentIndex n) :
    productFrameFourth n i j k l = productFrameFourth n j i k l := by
  unfold productFrameFourth
  congr 1
  funext s
  ring

theorem productFrameFourth_swap_last (n : ℕ) (i j k l : MomentIndex n) :
    productFrameFourth n i j k l = productFrameFourth n i j l k := by
  unfold productFrameFourth
  congr 1
  funext s
  ring

theorem productFrameMoment_transpose_input (n : ℕ)
    (A : Matrix (MomentIndex n) (MomentIndex n) ℝ) :
    productFrameMoment n Aᵀ = productFrameMoment n A := by
  ext i j
  unfold productFrameMoment
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp_rw [productFrameFourth_swap_last n i j]

theorem productFrameMoment_transpose_output (n : ℕ)
    (A : Matrix (MomentIndex n) (MomentIndex n) ℝ) :
    (productFrameMoment n A)ᵀ = productFrameMoment n A := by
  ext i j
  simp only [Matrix.transpose_apply, productFrameMoment,
    productFrameFourth_swap_first n j i]

/-- The real tensor channel kills all antisymmetric input. This permits using
the same four real frame vectors for complex coefficients. -/
theorem tensorMoment_transpose_input (n : ℕ)
    (A : Matrix (MomentIndex n) (MomentIndex n) ℝ) :
    tensorMoment n Aᵀ = tensorMoment n A := by
  have h := productFrameMoment_transpose_input n A
  rw [productFrameMoment_eq_tensorMoment, productFrameMoment_eq_tensorMoment] at h
  ext i j
  have hij := congrArg (fun M : Matrix (MomentIndex n) (MomentIndex n) ℝ => M i j) h
  change (2 : ℝ) ^ n * tensorMoment n Aᵀ i j =
    (2 : ℝ) ^ n * tensorMoment n A i j at hij
  exact mul_left_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0) hij

theorem tensorMoment_transpose_output (n : ℕ)
    (A : Matrix (MomentIndex n) (MomentIndex n) ℝ) :
    (tensorMoment n A)ᵀ = tensorMoment n A := by
  have h := productFrameMoment_transpose_output n A
  rw [productFrameMoment_eq_tensorMoment] at h
  ext i j
  have hij := congrArg (fun M : Matrix (MomentIndex n) (MomentIndex n) ℝ => M i j) h
  change (2 : ℝ) ^ n * tensorMoment n A j i =
    (2 : ℝ) ^ n * tensorMoment n A i j at hij
  exact mul_left_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0) hij

theorem tensorMoment_antisymmetric_eq_zero (n : ℕ)
    (A : Matrix (MomentIndex n) (MomentIndex n) ℝ) :
    tensorMoment n (A - Aᵀ) = 0 := by
  rw [map_sub, tensorMoment_transpose_input, sub_self]

end ComplementedSubspace
