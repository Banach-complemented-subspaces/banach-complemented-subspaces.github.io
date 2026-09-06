import ComplementedSubspace.FiniteSigns
import Mathlib.Analysis.Complex.Norm

noncomputable section
namespace ComplementedSubspace

/-- Complex scalar coefficients on the same cube of real signs. -/
def complexSignSum (n : ℕ) (a : Fin n → ℂ) (s : SignIndex n) : ℂ :=
  ⟨realSignSum n (fun i => (a i).re) s, realSignSum n (fun i => (a i).im) s⟩

theorem complexSignSum_norm_sq (n : ℕ) (a : Fin n → ℂ) (s : SignIndex n) :
    ‖complexSignSum n a s‖ ^ 2 =
      realSignSum n (fun i => (a i).re) s ^ 2 +
        realSignSum n (fun i => (a i).im) s ^ 2 := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, complexSignSum, pow_two]

theorem complexSignSum_second_moment (n : ℕ) (a : Fin n → ℂ) :
    finiteAverage (fun s => ‖complexSignSum n a s‖ ^ 2) = ∑ i, ‖a i‖ ^ 2 := by
  simp_rw [complexSignSum_norm_sq]
  rw [finiteAverage_add, realSignSum_second_moment, realSignSum_second_moment]
  simp_rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, pow_two, Finset.sum_add_distrib]

/-- The fourth-moment bound over complex scalars requires no complex Gaussian
theory; the real and imaginary parts share the same finite signs. -/
theorem complexSignSum_fourth_moment_le (n : ℕ) (a : Fin n → ℂ) :
    finiteAverage (fun s => ‖complexSignSum n a s‖ ^ 4) ≤
      3 * (∑ i, ‖a i‖ ^ 2) ^ 2 := by
  have hid (s : SignIndex n) : ‖complexSignSum n a s‖ ^ 4 =
      realSignSum n (fun i => (a i).re) s ^ 4 +
        2 * (realSignSum n (fun i => (a i).re) s ^ 2 *
          realSignSum n (fun i => (a i).im) s ^ 2) +
        realSignSum n (fun i => (a i).im) s ^ 4 := by
    calc
      ‖complexSignSum n a s‖ ^ 4 = (‖complexSignSum n a s‖ ^ 2) ^ 2 := by ring
      _ = (realSignSum n (fun i => (a i).re) s ^ 2 +
          realSignSum n (fun i => (a i).im) s ^ 2) ^ 2 := by
        rw [complexSignSum_norm_sq]
      _ = _ := by ring
  simp_rw [hid, finiteAverage_add, finiteAverage_mul]
  have hR := realSignSum_fourth_moment_le n (fun i => (a i).re)
  have hI := realSignSum_fourth_moment_le n (fun i => (a i).im)
  have hM := realSignSum_mixed_fourth_moment_le n
    (fun i => (a i).re) (fun i => (a i).im)
  have hn : (∑ i, ‖a i‖ ^ 2) =
      (∑ i, (a i).re ^ 2) + (∑ i, (a i).im ^ 2) := by
    simp_rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two, Finset.sum_add_distrib]
  rw [hn]
  nlinarith

end ComplementedSubspace
