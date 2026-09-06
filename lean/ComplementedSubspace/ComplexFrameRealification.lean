import ComplementedSubspace.ComplexFrameCoefficient
import ComplementedSubspace.ProductFrameSignSample

/-! A complex frame of order n, considered over the reals, is uniformly
isomorphic to the real frame of order n+1. Only one extra four-row factor is
introduced, so the comparison constant is independent of tensor order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal BigOperators
namespace ComplementedSubspace

def complexRealFrameRow (z : ℂ) (r : Fin 4) : ℝ :=
  z.re * realFrame r 0 + z.im * realFrame r 1

theorem complexRealFrameRow_second (z : ℂ) :
    finiteAverage (fun r => complexRealFrameRow z r ^ 2) = ‖z‖ ^ 2 := by
  have he (r : Fin 4) : complexRealFrameRow z r ^ 2 =
      z.re ^ 2 * (realFrame r 0 * realFrame r 0) +
      (2 * z.re * z.im) * (realFrame r 0 * realFrame r 1) +
      z.im ^ 2 * (realFrame r 1 * realFrame r 1) := by unfold complexRealFrameRow; ring
  simp_rw [he, finiteAverage_add, finiteAverage_mul, realFrame_covariance_entry]
  norm_num
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, pow_two]

theorem complexRealFrameRow_abs_le (z : ℂ) (r : Fin 4) :
    |complexRealFrameRow z r| ≤ 2 * ‖z‖ := by
  have hf := realFrame_length_sq r
  rw [Fin.sum_univ_two] at hf
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two]
  have hc : complexRealFrameRow z r ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
    unfold complexRealFrameRow
    nlinarith [sq_nonneg (z.re * realFrame r 1 - z.im * realFrame r 0)]
  have hn := norm_nonneg z
  have ha := abs_nonneg (complexRealFrameRow z r)
  have hasq := sq_abs (complexRealFrameRow z r)
  nlinarith [sq_nonneg ‖z‖]

private theorem nonneg_square_rpow_half (x : ℝ) (hx : 0 ≤ x) (p : ℝ) :
    (x ^ 2) ^ (p / 2) = x ^ p := by
  rw [← Real.rpow_natCast_mul hx]
  congr 1
  ring

theorem complexRealFrameRow_moment_lower (z : ℂ) (p : ℝ) (hp : 2 ≤ p) :
    ‖z‖ ^ p ≤ finiteAverage (fun r => |complexRealFrameRow z r| ^ p) := by
  have h := finiteAverage_rpow_le (fun r => complexRealFrameRow z r ^ 2)
    (fun _ => sq_nonneg _) (p / 2) (by linarith)
  rw [complexRealFrameRow_second, nonneg_square_rpow_half _ (norm_nonneg _)] at h
  have he (r : Fin 4) : (complexRealFrameRow z r ^ 2) ^ (p / 2) =
      |complexRealFrameRow z r| ^ p := by
    rw [← sq_abs, nonneg_square_rpow_half _ (abs_nonneg _)]
  simpa only [he] using h

theorem complexRealFrameRow_moment_upper (z : ℂ) (p : ℝ) (hp : 0 ≤ p) :
    finiteAverage (fun r => |complexRealFrameRow z r| ^ p) ≤ (2 : ℝ) ^ p * ‖z‖ ^ p := by
  calc
    _ ≤ finiteAverage (fun _ : Fin 4 => (2 * ‖z‖) ^ p) :=
      finiteAverage_mono _ _ fun r =>
        Real.rpow_le_rpow (abs_nonneg _) (complexRealFrameRow_abs_le z r) hp
    _ = _ := by rw [finiteAverage_const, Real.mul_rpow (by norm_num) (norm_nonneg _)]

def complexFrameRealificationLinearEquiv (n : ℕ) (p : ℝ) :
    ComplexFrameCoefficient n p ≃ₗ[ℝ] FrameCoefficient (n + 1) p where
  toFun c := Sum.elim (fun i => (c i).re) (fun i => (c i).im)
  invFun b := fun i => ⟨b (.inl i), b (.inr i)⟩
  left_inv c := by
    funext i
    exact Complex.ext rfl rfl
  right_inv b := by
    funext i
    cases i <;> rfl
  map_add' b c := by
    funext i
    cases i <;> rfl
  map_smul' a c := by
    funext i
    cases i with
    | inl i => exact Complex.smul_re a (c i)
    | inr i => exact Complex.smul_im a (c i)

theorem productFrameEval_complexRealification (n : ℕ) (p : ℝ)
    (c : ComplexFrameCoefficient n p) (r : Fin 4) (s : FrameIndex n) :
    productFrameEval (n + 1) (complexFrameRealificationLinearEquiv n p c) (r, s) =
      complexRealFrameRow (complexProductFrameEval n c s) r := by
  change (∑ i : MomentIndex n ⊕ MomentIndex n,
    (Sum.elim (fun j => (c j).re) (fun j => (c j).im) i) * realProductFrame (n + 1) (r, s) i) = _
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, realProductFrame,
    complexRealFrameRow, complexProductFrameEval_re, complexProductFrameEval_im,
    productFrameEval, Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem complexFrameRealification_norm_rpow (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) (c : ComplexFrameCoefficient n p) :
    ‖complexFrameRealificationLinearEquiv n p c‖ ^ p =
      finiteAverage (fun s : FrameIndex n => finiteAverage (fun r : Fin 4 =>
        |complexRealFrameRow (complexProductFrameEval n c s) r| ^ p)) := by
  rw [frameCoefficient_norm_rpow _ _ hp]
  change finiteAverage (fun rs : Fin 4 × FrameIndex n =>
    |productFrameEval (n + 1) (complexFrameRealificationLinearEquiv n p c) rs| ^ p) = _
  rw [finiteAverage_prod, finiteAverage_comm]
  apply congrArg finiteAverage
  funext s
  apply congrArg finiteAverage
  funext r
  exact congrArg (fun x : ℝ => |x| ^ p)
    (productFrameEval_complexRealification n p c r s)

theorem complexFrameRealification_norm_bounds (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) (c : ComplexFrameCoefficient n p) :
    ‖c‖ ≤ ‖complexFrameRealificationLinearEquiv n p c‖ ∧
      ‖complexFrameRealificationLinearEquiv n p c‖ ≤ 2 * ‖c‖ := by
  have hp0 : 0 < p := by linarith
  have hlo : ‖c‖ ^ p ≤ ‖complexFrameRealificationLinearEquiv n p c‖ ^ p := by
    rw [complexFrameCoefficient_norm_rpow _ _ hp0, complexFrameRealification_norm_rpow _ _ hp0]
    exact finiteAverage_mono _ _ fun s => complexRealFrameRow_moment_lower _ _ hp
  have hhi : ‖complexFrameRealificationLinearEquiv n p c‖ ^ p ≤ (2 * ‖c‖) ^ p := by
    rw [complexFrameRealification_norm_rpow _ _ hp0,
      Real.mul_rpow (by norm_num) (norm_nonneg _), complexFrameCoefficient_norm_rpow _ _ hp0,
      ← finiteAverage_mul]
    exact finiteAverage_mono _ _ fun s => complexRealFrameRow_moment_upper _ _ hp0.le
  exact ⟨(Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp0).mp hlo,
    (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hp0).mp hhi⟩

/-- Uniform real equivalence: forward norm at most two, inverse norm at most one. -/
def complexFrameRealification (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) :
    ComplexFrameCoefficient n p ≃L[ℝ] FrameCoefficient (n + 1) p :=
  (complexFrameRealificationLinearEquiv n p).toContinuousLinearEquivOfBounds 2 1
    (fun c => (complexFrameRealification_norm_bounds n p hp c).2)
    (fun b => by
      have h := (complexFrameRealification_norm_bounds n p hp
        ((complexFrameRealificationLinearEquiv n p).symm b)).1
      simpa only [LinearEquiv.apply_symm_apply, one_mul] using h)

theorem complexFrameRealification_norm_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) :
    ‖(complexFrameRealification n p hp).toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  exact fun c => (complexFrameRealification_norm_bounds n p hp c).2

theorem complexFrameRealification_symm_norm_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) :
    ‖(complexFrameRealification n p hp).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro b
  change ‖(complexFrameRealificationLinearEquiv n p).symm b‖ ≤ 1 * ‖b‖
  have h := (complexFrameRealification_norm_bounds n p hp
    ((complexFrameRealificationLinearEquiv n p).symm b)).1
  simpa only [LinearEquiv.apply_symm_apply, one_mul] using h

end ComplementedSubspace
