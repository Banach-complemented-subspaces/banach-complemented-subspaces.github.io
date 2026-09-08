import ComplementedSubspace.ProductFrame

noncomputable section
namespace ComplementedSubspace
open Matrix

-- These local transparency hints concern only coordinate types. No norm or
-- algebraic instance is changed. The option permits changing elaborator
-- transparency locally; all resulting proof terms still pass the kernel.
set_option allowUnsafeReducibility true in
attribute [local reducible] Matrix MomentIndex FrameIndex

/-- Entrywise fourth-moment kernel of the actual finite product frame. -/
def productFrameFourth (n : ℕ) (i j k l : MomentIndex n) : ℝ :=
  finiteAverage (fun s => realProductFrame n s i * realProductFrame n s j *
    realProductFrame n s k * realProductFrame n s l)

private def sideIndex {ι : Type*} (b : Bool) (i : ι) : ι ⊕ ι :=
  if b then Sum.inr i else Sum.inl i

private theorem sideIndex_false {ι : Type*} (i : ι) : sideIndex false i = Sum.inl i := rfl
private theorem sideIndex_true {ι : Type*} (i : ι) : sideIndex true i = Sum.inr i := rfl

private def sideFrame (s : Fin 4) (b : Bool) : ℝ :=
  if b then realFrame s 1 else realFrame s 0

private theorem realProductFrame_side (n : ℕ) (s : FrameIndex (n + 1))
    (b : Bool) (i : MomentIndex n) :
    realProductFrame (n + 1) s (sideIndex b i) =
      sideFrame s.1 b * realProductFrame n s.2 i := by
  cases b <;> rfl

private theorem four_products (a b c d x y z t : ℝ) :
    (a * x) * (b * y) * (c * z) * (d * t) =
      (a * b * c * d) * (x * y * z * t) := by ring

private theorem sideFrame_fourth (a b c d : Bool) :
    finiteAverage (fun s : Fin 4 => sideFrame s a * sideFrame s b *
      sideFrame s c * sideFrame s d) =
      ((if a = b ∧ c = d then 1 else 0) +
        (if a = c ∧ b = d then 1 else 0) +
        (if a = d ∧ b = c then 1 else 0) : ℝ) / 2 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [finiteAverage, sideFrame, realFrame, Fin.sum_univ_succ,
      Real.mul_self_sqrt] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem productFrameFourth_succ (n : ℕ) (a b c d : Bool)
    (i j k l : MomentIndex n) :
    productFrameFourth (n + 1) (sideIndex a i) (sideIndex b j)
      (sideIndex c k) (sideIndex d l) =
      (((if a = b ∧ c = d then 1 else 0) +
        (if a = c ∧ b = d then 1 else 0) +
        (if a = d ∧ b = c then 1 else 0) : ℝ) / 2) *
        productFrameFourth n i j k l := by
  unfold productFrameFourth
  change finiteAverage (fun s : Fin 4 × FrameIndex n =>
    realProductFrame (n + 1) s (sideIndex a i) *
      realProductFrame (n + 1) s (sideIndex b j) *
      realProductFrame (n + 1) s (sideIndex c k) *
      realProductFrame (n + 1) s (sideIndex d l)) = _
  simp_rw [realProductFrame_side]
  conv_lhs => arg 1; intro s; rw [four_products]
  rw [finiteAverage_separated
    (fun r : Fin 4 => sideFrame r a * sideFrame r b * sideFrame r c * sideFrame r d)
    (fun t : FrameIndex n => realProductFrame n t i * realProductFrame n t j *
      realProductFrame n t k * realProductFrame n t l), sideFrame_fourth]

/-- The linear matrix map supplied by the finite frame's fourth moments. -/
def productFrameMoment (n : ℕ) (A : Matrix (MomentIndex n) (MomentIndex n) ℝ) :
    Matrix (MomentIndex n) (MomentIndex n) ℝ :=
  fun i j => ∑ k, ∑ l, productFrameFourth n i j k l * A k l

theorem productFrameMoment_add (n : ℕ)
    (A B : Matrix (MomentIndex n) (MomentIndex n) ℝ) :
    productFrameMoment n (A + B) = productFrameMoment n A + productFrameMoment n B := by
  ext i j
  simp [productFrameMoment, mul_add, Finset.sum_add_distrib]

/-- The concrete finite fourth-moment map is exactly the previously verified
tensor map, with the normalization for frame vectors of length `sqrt (2^n)`. -/
theorem productFrameMoment_eq_tensorMoment (n : ℕ)
    (A : Matrix (MomentIndex n) (MomentIndex n) ℝ) :
    productFrameMoment n A = (2 : ℝ) ^ n • tensorMoment n A := by
  induction n with
  | zero =>
    ext i j
    cases i
    cases j
    simp [productFrameMoment, productFrameFourth, realProductFrame,
      finiteAverage, tensorMoment, MomentIndex, FrameIndex, Fintype.card_unit]
  | succ n ih =>
    have hs : productFrameMoment (n + 1) A =
        (2 : ℝ) • circleBlock
          (productFrameMoment n (A.submatrix Sum.inl Sum.inl))
          (productFrameMoment n (A.submatrix Sum.inr Sum.inr))
          (productFrameMoment n (A.submatrix Sum.inl Sum.inr +
            A.submatrix Sum.inr Sum.inl)) := by
      ext i j
      change (∑ k : MomentIndex n ⊕ MomentIndex n,
        ∑ l : MomentIndex n ⊕ MomentIndex n,
          productFrameFourth (n + 1) i j k l * A k l) = _
      cases i <;> cases j
      all_goals
        simp only [productFrameMoment, Fintype.sum_sum_type, Finset.sum_add_distrib,
          ← sideIndex_false, ← sideIndex_true, productFrameFourth_succ]
        simp only [Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true,
          and_self, and_true, and_false, ↓reduceIte, zero_add, add_zero,
          zero_mul, one_mul, Finset.sum_const_zero, circleBlock,
          Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.add_apply,
          Matrix.submatrix_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sideIndex, ↓reduceIte]
        simp only [productFrameMoment, Matrix.submatrix_apply, Pi.add_apply,
          Matrix.add_apply, mul_add, Finset.sum_add_distrib,
          Finset.sum_const_zero, zero_add, add_zero, ← Finset.mul_sum,
          ← Finset.sum_mul]
        norm_num
        simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul,
          Finset.sum_const_zero, zero_add, add_zero]
        first | rfl | ring
    rw [hs, ih, ih, ih]
    let X := tensorMoment n (A.submatrix Sum.inl Sum.inl)
    let Y := tensorMoment n (A.submatrix Sum.inr Sum.inr)
    let H := tensorMoment n (A.submatrix Sum.inl Sum.inr + A.submatrix Sum.inr Sum.inl)
    change (2 : ℝ) • circleBlock ((2 : ℝ) ^ n • X) ((2 : ℝ) ^ n • Y)
      ((2 : ℝ) ^ n • H) = (2 : ℝ) ^ (n + 1) • circleBlock X Y H
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change 2 * ((1 / 4 : ℝ) * (3 * (2 ^ n * X i j) + 2 ^ n * Y i j)) =
          2 ^ (n + 1) * ((1 / 4 : ℝ) * (3 * X i j + Y i j))
        rw [pow_succ]
        ring
      | inr j =>
        change 2 * ((1 / 4 : ℝ) * (2 ^ n * H i j)) =
          2 ^ (n + 1) * ((1 / 4 : ℝ) * H i j)
        rw [pow_succ]
        ring
    | inr i =>
      cases j with
      | inl j =>
        change 2 * ((1 / 4 : ℝ) * (2 ^ n * H i j)) =
          2 ^ (n + 1) * ((1 / 4 : ℝ) * H i j)
        rw [pow_succ]
        ring
      | inr j =>
        change 2 * ((1 / 4 : ℝ) * (2 ^ n * X i j + 3 * (2 ^ n * Y i j))) =
          2 ^ (n + 1) * ((1 / 4 : ℝ) * (X i j + 3 * Y i j))
        rw [pow_succ]
        ring

private theorem square_sum_mul_square_sum {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, f i) ^ 2 * (∑ i, g i) ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, (f i * f j) * (g k * g l) := by
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]

/-- The fourth moment for two actual coefficient evaluations. -/
theorem productFrameEval_paired_fourth_moment (n : ℕ)
    (b c : MomentIndex n → ℝ) :
    finiteAverage (fun s => productFrameEval n b s ^ 2 * productFrameEval n c s ^ 2) =
      (2 : ℝ) ^ n * hsInner (rankOne b) (tensorMoment n (rankOne c)) := by
  have h : finiteAverage (fun s =>
      productFrameEval n b s ^ 2 * productFrameEval n c s ^ 2) =
      hsInner (rankOne b) (productFrameMoment n (rankOne c)) := by
    simp only [productFrameEval, square_sum_mul_square_sum]
    simp_rw [finiteAverage_sum]
    simp only [hsInner, productFrameMoment, rankOne, Matrix.vecMulVec_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    have hid (s : FrameIndex n) :
        (b i * realProductFrame n s i) * (b j * realProductFrame n s j) *
          ((c k * realProductFrame n s k) * (c l * realProductFrame n s l)) =
        (b i * b j * (c k * c l)) *
          (realProductFrame n s i * realProductFrame n s j *
            realProductFrame n s k * realProductFrame n s l) := by ring
    simp_rw [hid, finiteAverage_mul]
    unfold productFrameFourth
    ring
  rw [h, productFrameMoment_eq_tensorMoment, tensor_hsInner_smul_right]

end ComplementedSubspace
