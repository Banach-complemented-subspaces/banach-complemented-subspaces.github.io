import ComplementedSubspace.ProductFrameIndex
import ComplementedSubspace.FiniteFrame
import ComplementedSubspace.FiniteSigns

noncomputable section
namespace ComplementedSubspace
open Matrix

/-- The actual four-point product frame, in the binary coefficient coordinates
used by `tensorMoment`. Its ambient counting dimension is `4^n`. -/
def realProductFrame : (n : ℕ) → Matrix (FrameIndex n) (MomentIndex n) ℝ
  | 0, _, _ => 1
  | n + 1, s, Sum.inl i => realFrame s.1 0 * realProductFrame n s.2 i
  | n + 1, s, Sum.inr i => realFrame s.1 1 * realProductFrame n s.2 i

theorem momentIndex_card (n : ℕ) : Fintype.card (MomentIndex n) = 2 ^ n := by
  induction n with
  | zero => exact Fintype.card_unit
  | succ n ih =>
    change Fintype.card (MomentIndex n ⊕ MomentIndex n) = _
    rw [Fintype.card_sum, ih, pow_succ]
    omega

theorem finiteAverage_mul_right {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    finiteAverage (fun i => f i * c) = finiteAverage f * c := by
  simpa only [mul_comm] using finiteAverage_mul c f

theorem finiteAverage_separated {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℝ) (g : κ → ℝ) :
    finiteAverage (fun s : ι × κ => f s.1 * g s.2) =
      finiteAverage f * finiteAverage g := by
  rw [finiteAverage_prod]
  simp_rw [finiteAverage_mul]
  rw [finiteAverage_mul_right]

theorem realFrame_covariance_entry (i j : Fin 2) :
    finiteAverage (fun s : Fin 4 => realFrame s i * realFrame s j) =
      if i = j then 1 else 0 := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) realFrame_covariance
  simpa [finiteAverage, rankOne, Matrix.one_apply, Finset.sum_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply] using h

theorem realProductFrame_covariance (n : ℕ) (i j : MomentIndex n) :
    finiteAverage (fun s => realProductFrame n s i * realProductFrame n s j) =
      if i = j then 1 else 0 := by
  induction n with
  | zero =>
    cases i
    cases j
    simp [realProductFrame, finiteAverage, MomentIndex, Fintype.card_unit]
  | succ n ih =>
    have hsep (a b : Fin 2) (i j : MomentIndex n) :
        finiteAverage (fun s : Fin 4 × FrameIndex n =>
          (realFrame s.1 a * realFrame s.1 b) *
            (realProductFrame n s.2 i * realProductFrame n s.2 j)) =
          finiteAverage (fun r : Fin 4 => realFrame r a * realFrame r b) *
            finiteAverage (fun t : FrameIndex n =>
              realProductFrame n t i * realProductFrame n t j) :=
      finiteAverage_separated
        (fun r : Fin 4 => realFrame r a * realFrame r b)
        (fun t : FrameIndex n => realProductFrame n t i * realProductFrame n t j)
    change finiteAverage (fun s : Fin 4 × FrameIndex n =>
      realProductFrame (n + 1) s i * realProductFrame (n + 1) s j) = _
    cases i <;> cases j <;>
      simp only [realProductFrame]
    all_goals
      conv_lhs => arg 1; intro s; rw [mul_mul_mul_comm]
      rw [hsep, realFrame_covariance_entry, ih]
      simp [MomentIndex, Sum.inl.injEq, Sum.inr.injEq]

theorem realProductFrame_length_sq (n : ℕ) (s : FrameIndex n) :
    (∑ i, realProductFrame n s i ^ 2) = (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [realProductFrame, MomentIndex] <;> rfl
  | succ n ih =>
    change (∑ i : MomentIndex n ⊕ MomentIndex n,
      realProductFrame (n + 1) s i ^ 2) = _
    rw [Fintype.sum_sum_type]
    simp only [realProductFrame, mul_pow, ← Finset.mul_sum, ih]
    have h := realFrame_length_sq s.1
    rw [Fin.sum_univ_two] at h
    rw [pow_succ (2 : ℝ) n]
    nlinarith [congrArg (fun r : ℝ => r * (2 : ℝ) ^ n) h]

/-- Scalar frame evaluation. Normalizing its finite `ell_p` norm by the
sample cardinality gives the proposed coefficient-space norm. -/
def productFrameEval (n : ℕ) (b : MomentIndex n → ℝ) (s : FrameIndex n) : ℝ :=
  ∑ i, b i * realProductFrame n s i

theorem productFrameEval_covariance (n : ℕ) (b c : MomentIndex n → ℝ) :
    finiteAverage (fun s => productFrameEval n b s * productFrameEval n c s) =
      ∑ i, b i * c i := by
  simp only [productFrameEval, Finset.sum_mul, Finset.mul_sum]
  rw [finiteAverage_sum]
  simp_rw [finiteAverage_sum]
  have h (i j : MomentIndex n) :
      finiteAverage (fun s => b i * realProductFrame n s i *
        (c j * realProductFrame n s j)) =
        b i * c j * (if i = j then 1 else 0) := by
    simp_rw [mul_mul_mul_comm]
    rw [finiteAverage_mul, realProductFrame_covariance]
  simp_rw [h]
  simp

theorem productFrameEval_second_moment (n : ℕ) (b : MomentIndex n → ℝ) :
    finiteAverage (fun s => productFrameEval n b s ^ 2) = ∑ i, b i ^ 2 := by
  simpa only [pow_two] using productFrameEval_covariance n b b

theorem productFrameEval_injective (n : ℕ) : Function.Injective (productFrameEval n) := by
  intro b c h
  have hz : finiteAverage (fun s => productFrameEval n (b - c) s ^ 2) = 0 := by
    have he (s : FrameIndex n) : productFrameEval n (b - c) s = 0 := by
      have hs := congrFun h s
      simpa [productFrameEval, sub_mul, Finset.sum_sub_distrib] using sub_eq_zero.mpr hs
    simp_rw [he]
    simp [finiteAverage]
  rw [productFrameEval_second_moment] at hz
  ext i
  have hi : (b i - c i) ^ 2 ≤ ∑ j, (b j - c j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (b j - c j)) (Finset.mem_univ i)
  change (∑ j, (b j - c j) ^ 2) = 0 at hz
  nlinarith [sq_nonneg (b i - c i)]

end ComplementedSubspace
