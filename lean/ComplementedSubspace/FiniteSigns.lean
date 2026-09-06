import ComplementedSubspace.TensorMoment
import Mathlib.Algebra.BigOperators.Expect

/-! Finite Rademacher averages. These replace the manuscript's Gaussian
coefficient vectors where only covariance and fourth moments are used. -/

noncomputable section
namespace ComplementedSubspace
open scoped BigOperators

/-- The ordinary uniform average on a finite sample space. -/
def finiteAverage {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i

theorem finiteAverage_add {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    finiteAverage (fun i => f i + g i) = finiteAverage f + finiteAverage g := by
  simp [finiteAverage, Finset.sum_add_distrib, mul_add]

theorem finiteAverage_sub {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    finiteAverage (fun i => f i - g i) = finiteAverage f - finiteAverage g := by
  simp [finiteAverage, Finset.sum_sub_distrib, mul_sub]

theorem finiteAverage_mul {ι : Type*} [Fintype ι] (c : ℝ) (f : ι → ℝ) :
    finiteAverage (fun i => c * f i) = c * finiteAverage f := by
  simp [finiteAverage, ← Finset.mul_sum, mul_left_comm]

theorem finiteAverage_const {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℝ) :
    finiteAverage (fun _ : ι => c) = c := by
  simp [finiteAverage, Fintype.card_ne_zero]

theorem finiteAverage_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : 0 ≤ finiteAverage f := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun i _ => hf i)

theorem finiteAverage_mono {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hfg : ∀ i, f i ≤ g i) : finiteAverage f ≤ finiteAverage g := by
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => hfg i)) (by positivity)

theorem finiteAverage_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → ℝ) :
    finiteAverage (fun i => ∑ j, f i j) = ∑ j, finiteAverage (fun i => f i j) := by
  simp only [finiteAverage, Finset.mul_sum]
  exact Finset.sum_comm

theorem finiteAverage_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι × κ → ℝ) :
    finiteAverage f = finiteAverage (fun i => finiteAverage (fun j => f (i, j))) := by
  simp only [finiteAverage, Fintype.card_prod, Nat.cast_mul, mul_inv,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem finiteAverage_bool (f : Bool → ℝ) :
    finiteAverage f = (f false + f true) / 2 := by
  simp [finiteAverage, Fintype.sum_bool]
  ring

theorem finiteAverage_bool_prod {ι : Type*} [Fintype ι]
    (f : Bool × ι → ℝ) :
    finiteAverage f = finiteAverage (fun i => (f (false, i) + f (true, i)) / 2) := by
  rw [finiteAverage_prod, finiteAverage_bool]
  simp only [div_eq_mul_inv, mul_comm _ (2 : ℝ)⁻¹]
  rw [finiteAverage_mul, finiteAverage_add]

/-- Recursive finite cube with one independent real sign in each coordinate. -/
def SignIndex : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × SignIndex n

instance signIndexFintype : (n : ℕ) → Fintype (SignIndex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd Bool (SignIndex n)
      inferInstance (signIndexFintype n)

instance signIndexNonempty : (n : ℕ) → Nonempty (SignIndex n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n + 1 => let ⟨s⟩ := signIndexNonempty n; ⟨(false, s)⟩

def signValue (b : Bool) : ℝ := if b then 1 else -1

/-- Scalar linear combination of the independent signs. -/
def realSignSum : (n : ℕ) → (Fin n → ℝ) → SignIndex n → ℝ
  | 0, _, _ => 0
  | n + 1, a, s => signValue s.1 * a 0 + realSignSum n (fun i => a i.succ) s.2

theorem realSignSum_second_moment (n : ℕ) (a : Fin n → ℝ) :
    finiteAverage (fun s => realSignSum n a s ^ 2) = ∑ i, a i ^ 2 := by
  induction n with
  | zero => simp [realSignSum, finiteAverage]
  | succ n ih =>
    change finiteAverage (fun s : Bool × SignIndex n =>
      (signValue s.1 * a 0 + realSignSum n (fun i => a i.succ) s.2) ^ 2) = _
    rw [finiteAverage_bool_prod]
    have hid (y : ℝ) : ((-1 * a 0 + y) ^ 2 + (1 * a 0 + y) ^ 2) / 2 =
        a 0 ^ 2 + y ^ 2 := by ring
    simp only [signValue, Bool.false_eq_true, ↓reduceIte, hid]
    rw [finiteAverage_add, finiteAverage_const, ih, Fin.sum_univ_succ]

/-- Exact fourth moment, including the usual nonnegative correction term. -/
theorem realSignSum_fourth_moment (n : ℕ) (a : Fin n → ℝ) :
    finiteAverage (fun s => realSignSum n a s ^ 4) =
      3 * (∑ i, a i ^ 2) ^ 2 - 2 * ∑ i, a i ^ 4 := by
  induction n with
  | zero => simp [realSignSum, finiteAverage]
  | succ n ih =>
    change finiteAverage (fun s : Bool × SignIndex n =>
      (signValue s.1 * a 0 + realSignSum n (fun i => a i.succ) s.2) ^ 4) = _
    rw [finiteAverage_bool_prod]
    have hid (y : ℝ) : ((-1 * a 0 + y) ^ 4 + (1 * a 0 + y) ^ 4) / 2 =
        a 0 ^ 4 + 6 * a 0 ^ 2 * y ^ 2 + y ^ 4 := by ring
    simp only [signValue, Bool.false_eq_true, ↓reduceIte, hid]
    rw [finiteAverage_add, finiteAverage_add, finiteAverage_const,
      finiteAverage_mul, realSignSum_second_moment, ih]
    simp only [Fin.sum_univ_succ]
    ring

theorem realSignSum_fourth_moment_le (n : ℕ) (a : Fin n → ℝ) :
    finiteAverage (fun s => realSignSum n a s ^ 4) ≤
      3 * (∑ i, a i ^ 2) ^ 2 := by
  rw [realSignSum_fourth_moment]
  have h : 0 ≤ ∑ i, a i ^ 4 := Finset.sum_nonneg (fun _ _ => by positivity)
  linarith

/-- Covariance identity for two scalar linear combinations. -/
theorem realSignSum_covariance (n : ℕ) (a b : Fin n → ℝ) :
    finiteAverage (fun s => realSignSum n a s * realSignSum n b s) =
      ∑ i, a i * b i := by
  induction n with
  | zero => simp [realSignSum, finiteAverage]
  | succ n ih =>
    change finiteAverage (fun s : Bool × SignIndex n =>
      (signValue s.1 * a 0 + realSignSum n (fun i => a i.succ) s.2) *
      (signValue s.1 * b 0 + realSignSum n (fun i => b i.succ) s.2)) = _
    rw [finiteAverage_bool_prod]
    have hid (y z : ℝ) : ((-1 * a 0 + y) * (-1 * b 0 + z) +
        (1 * a 0 + y) * (1 * b 0 + z)) / 2 = a 0 * b 0 + y * z := by ring
    simp only [signValue, Bool.false_eq_true, ↓reduceIte, hid]
    rw [finiteAverage_add, finiteAverage_const, ih, Fin.sum_univ_succ]

/-- Mixed fourth moment, useful for complex coefficients split into real and
imaginary parts. It is proved on the same real sign cube. -/
theorem realSignSum_mixed_fourth_moment (n : ℕ) (a b : Fin n → ℝ) :
    finiteAverage (fun s => realSignSum n a s ^ 2 * realSignSum n b s ^ 2) =
      (∑ i, a i ^ 2) * (∑ i, b i ^ 2) + 2 * (∑ i, a i * b i) ^ 2 -
        2 * ∑ i, a i ^ 2 * b i ^ 2 := by
  induction n with
  | zero => simp [realSignSum, finiteAverage]
  | succ n ih =>
    change finiteAverage (fun s : Bool × SignIndex n =>
      (signValue s.1 * a 0 + realSignSum n (fun i => a i.succ) s.2) ^ 2 *
      (signValue s.1 * b 0 + realSignSum n (fun i => b i.succ) s.2) ^ 2) = _
    rw [finiteAverage_bool_prod]
    have hid (y z : ℝ) : ((-1 * a 0 + y) ^ 2 * (-1 * b 0 + z) ^ 2 +
        (1 * a 0 + y) ^ 2 * (1 * b 0 + z) ^ 2) / 2 =
        a 0 ^ 2 * b 0 ^ 2 + a 0 ^ 2 * z ^ 2 + b 0 ^ 2 * y ^ 2 +
          (4 * a 0 * b 0) * (y * z) + y ^ 2 * z ^ 2 := by ring
    simp only [signValue, Bool.false_eq_true, ↓reduceIte, hid]
    simp_rw [finiteAverage_add, finiteAverage_const, finiteAverage_mul]
    rw [realSignSum_second_moment, realSignSum_second_moment,
      realSignSum_covariance, ih]
    simp only [Fin.sum_univ_succ]
    ring

theorem realSignSum_mixed_fourth_moment_le (n : ℕ) (a b : Fin n → ℝ) :
    finiteAverage (fun s => realSignSum n a s ^ 2 * realSignSum n b s ^ 2) ≤
      3 * (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by
  rw [realSignSum_mixed_fourth_moment]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hnon : 0 ≤ ∑ i, a i ^ 2 * b i ^ 2 :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  nlinarith

theorem realSignSum_add (n : ℕ) (a b : Fin n → ℝ) (s : SignIndex n) :
    realSignSum n (a + b) s = realSignSum n a s + realSignSum n b s := by
  induction n with
  | zero => simp [realSignSum]
  | succ n ih =>
    rcases s with ⟨c, s⟩
    change signValue c * (a 0 + b 0) +
      realSignSum n ((fun i => a i.succ) + (fun i => b i.succ)) s = _
    rw [ih]
    simp only [realSignSum]
    ring

theorem realSignSum_mul (n : ℕ) (c : ℝ) (a : Fin n → ℝ) (s : SignIndex n) :
    realSignSum n (fun i => c * a i) s = c * realSignSum n a s := by
  induction n with
  | zero => simp [realSignSum]
  | succ n ih => simp [realSignSum, ih]; ring

/-- The actual coordinate sign vector represented by a cube sample. -/
def realSignVector : (n : ℕ) → SignIndex n → Fin n → ℝ
  | 0, _ => Fin.elim0
  | n + 1, s => Fin.cons (signValue s.1) (realSignVector n s.2)

theorem realSignVector_coordinate_sq (n : ℕ) (s : SignIndex n) (i : Fin n) :
    realSignVector n s i ^ 2 = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · change signValue s.1 ^ 2 = 1
      cases s.1 <;> norm_num [signValue]
    · exact ih s.2 i

theorem realSignVector_length_sq (n : ℕ) (s : SignIndex n) :
    (∑ i, realSignVector n s i ^ 2) = (n : ℝ) := by
  simp [realSignVector_coordinate_sq]

theorem realSignSum_eq_dot (n : ℕ) (a : Fin n → ℝ) (s : SignIndex n) :
    realSignSum n a s = ∑ i, a i * realSignVector n s i := by
  induction n with
  | zero => simp [realSignSum]
  | succ n ih =>
    simp only [realSignSum, Fin.sum_univ_succ, realSignVector, Fin.cons_zero,
      Fin.cons_succ, ih]
    ring

/-- A normalized coefficient vector has deterministic Euclidean length one,
which is stronger than the Gaussian second-moment assertion it replaces. -/
theorem normalizedRealSignVector_length_sq (n : ℕ) (hn : 0 < n) (s : SignIndex n) :
    (∑ i, ((Real.sqrt n)⁻¹ * realSignVector n s i) ^ 2) = 1 := by
  simp only [mul_pow, ← Finset.mul_sum, realSignVector_length_sq, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  have hne : (n : ℝ) ≠ 0 := by positivity
  exact inv_mul_cancel₀ hne

end ComplementedSubspace
