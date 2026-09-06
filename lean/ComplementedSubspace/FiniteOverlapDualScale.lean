import ComplementedSubspace.FiniteOverlapScale

/-! The extra factor two from dual subspace renorming fits the same recursion. -/

noncomputable section
namespace ComplementedSubspace

theorem finite_frame_dual_selection_scalar_bounds (n : ℕ) (p D K : ℝ)
    (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3) (hD : 2 ≤ D) (hK : 0 ≤ K)
    (hDK : 16 * K ≤ D) (hL : D ^ 8 < realFrameOverlapScale n p) :
    (((2 : ℝ) ^ n * realFrameSignConstant p / realFrameWitnessScale n p) *
        (2 * D) * K ^ 2 ≤ (2 : ℝ) ^ n / 4) ∧
    256 * K ^ 2 * realFrameSignConstant p ^ 2 * ((2 * D) * K) ^ 3 <
      realFrameOverlapScale n p := by
  have hD0 : 0 ≤ D := by linarith
  obtain ⟨hsmall, hsep⟩ := finite_frame_selection_scalar_bounds n p D (2 * K)
    hp₂ hp₃ hD (by positivity) (by linarith) hL
  have ha : 0 ≤ (2 : ℝ) ^ n * realFrameSignConstant p / realFrameWitnessScale n p := by
    apply div_nonneg
    · exact mul_nonneg (pow_nonneg (by norm_num) n)
        (Real.rpow_nonneg (by norm_num) _)
    · exact (Real.exp_pos _).le
  constructor
  · apply le_trans _ hsmall
    have hh : (2 * D) * K ^ 2 ≤ D * (2 * K) ^ 2 := by
      nlinarith [mul_nonneg hD0 (sq_nonneg K)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh ha
  · apply lt_of_le_of_lt _ hsep
    have hh : 0 ≤ 256 * (2 * K) ^ 2 * realFrameSignConstant p ^ 2 * (D * (2 * K)) ^ 3 := by
      positivity
    calc
      _ = (256 * (2 * K) ^ 2 * realFrameSignConstant p ^ 2 * (D * (2 * K)) ^ 3) / 4 := by ring
      _ ≤ _ := div_le_self hh (by norm_num)

end ComplementedSubspace
