import ComplementedSubspace.ProductFrameWitness
import ComplementedSubspace.FiniteSignsInterpolation

/-!
# Normalized frame rows and their dual norm bound

All four normalized one-factor rows have the same absolute evaluation moments.
Finite product averages propagate this identity to every product row. Covariance
and finite Hölder then produce actual continuous coefficient-space functionals.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ENNReal

namespace ComplementedSubspace

/-- The explicit unit Euclidean row used in the overlap randomization. -/
def normalizedProductFrameRow (n : ℕ) (s : FrameIndex n) : MomentIndex n → ℝ :=
  fun i => (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * realProductFrame n s i

def frameCoefficientRow (n : ℕ) (p : ℝ) (s : FrameIndex n) : FrameCoefficient n p :=
  normalizedProductFrameRow n s

theorem normalizedProductFrameRow_length_sq (n : ℕ) (s : FrameIndex n) :
    (∑ i, normalizedProductFrameRow n s i ^ 2) = 1 := by
  simp only [normalizedProductFrameRow, mul_pow, ← Finset.mul_sum,
    realProductFrame_length_sq, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ) ^ n)]
  exact inv_mul_cancel₀ (by positivity)

theorem normalizedProductFrameRow_covariance (n : ℕ) (i j : MomentIndex n) :
    finiteAverage (fun s =>
      normalizedProductFrameRow n s i * normalizedProductFrameRow n s j) =
      (if i = j then 1 else 0) / (2 : ℝ) ^ n := by
  have he (s : FrameIndex n) :
      normalizedProductFrameRow n s i * normalizedProductFrameRow n s j =
        (Real.sqrt ((2 : ℝ) ^ n))⁻¹ ^ 2 *
          (realProductFrame n s i * realProductFrame n s j) := by
    unfold normalizedProductFrameRow
    ring
  simp_rw [he]
  rw [finiteAverage_mul, realProductFrame_covariance, inv_pow,
    Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ) ^ n)]
  ring

private def frameRowKernel (s t : Fin 4) : ℝ :=
  (Real.sqrt 2)⁻¹ * (realFrame s 0 * realFrame t 0 + realFrame s 1 * realFrame t 1)

private theorem frameRowKernel_eq (s t : Fin 4) :
    frameRowKernel s t =
      (![![Real.sqrt 2, 0, 1, 1], ![0, Real.sqrt 2, 1, -1],
        ![1, 1, Real.sqrt 2, 0], ![1, -1, 0, Real.sqrt 2]] : Matrix (Fin 4) (Fin 4) ℝ) s t := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hz : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  fin_cases s <;> fin_cases t <;> norm_num [frameRowKernel, realFrame]
  all_goals field_simp
  all_goals nlinarith

private theorem frameRowKernel_moment (s : Fin 4) {p : ℝ} (hp : 0 < p) :
    finiteAverage (fun t : Fin 4 => |frameRowKernel s t| ^ p) =
      ((2 : ℝ) ^ (p / 2) + 2) / 4 := by
  have hs : Real.sqrt 2 ^ p = (2 : ℝ) ^ (p / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simp_rw [frameRowKernel_eq]
  fin_cases s <;>
    norm_num [finiteAverage, Fin.sum_univ_succ, Real.zero_rpow hp.ne',
      abs_of_nonneg (Real.sqrt_nonneg 2), hs] <;> ring

private def productFrameGram (n : ℕ) (s t : FrameIndex n) : ℝ :=
  ∑ i, realProductFrame n s i * realProductFrame n t i

private theorem productFrameGram_succ (n : ℕ) (s t : FrameIndex (n + 1)) :
    productFrameGram (n + 1) s t =
      (realFrame s.1 0 * realFrame t.1 0 + realFrame s.1 1 * realFrame t.1 1) *
        productFrameGram n s.2 t.2 := by
  change (∑ i : MomentIndex n ⊕ MomentIndex n, _) = _
  rw [Fintype.sum_sum_type]
  simp only [realProductFrame, productFrameGram, add_mul, Finset.mul_sum,
    Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

private theorem normalizedProductFrameRow_eval (n : ℕ) (s t : FrameIndex n) :
    productFrameEval n (normalizedProductFrameRow n s) t =
      (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * productFrameGram n s t := by
  simp only [productFrameEval, normalizedProductFrameRow, productFrameGram,
    mul_assoc, Finset.mul_sum]

theorem normalizedProductFrameRow_eval_succ (n : ℕ) (s t : FrameIndex (n + 1)) :
    productFrameEval (n + 1) (normalizedProductFrameRow (n + 1) s) t =
      (Real.sqrt 2)⁻¹ * (realFrame s.1 0 * realFrame t.1 0 +
        realFrame s.1 1 * realFrame t.1 1) *
          productFrameEval n (normalizedProductFrameRow n s.2) t.2 := by
  rw [normalizedProductFrameRow_eval, normalizedProductFrameRow_eval,
    productFrameGram_succ, pow_succ, Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ n),
    mul_inv_rev]
  ring

/-- Every row, including the diagonal rows, has the same exact product moment. -/
theorem normalizedProductFrameRow_moment (n : ℕ) (s : FrameIndex n)
    {p : ℝ} (hp : 0 < p) :
    finiteAverage (fun t => |productFrameEval n (normalizedProductFrameRow n s) t| ^ p) =
      (((2 : ℝ) ^ (p / 2) + 2) / 4) ^ n := by
  induction n with
  | zero =>
    simp [productFrameEval, normalizedProductFrameRow, realProductFrame,
      MomentIndex, finiteAverage]
  | succ n ih =>
    change finiteAverage (fun t : Fin 4 × FrameIndex n => _) = _
    simp only [normalizedProductFrameRow_eval_succ]
    change finiteAverage (fun t : Fin 4 × FrameIndex n =>
      |frameRowKernel s.1 t.1 *
        productFrameEval n (normalizedProductFrameRow n s.2) t.2| ^ p) = _
    simp only [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    rw [finiteAverage_separated (fun r => |frameRowKernel s.1 r| ^ p)
      (fun t => |productFrameEval n (normalizedProductFrameRow n s.2) t| ^ p),
      frameRowKernel_moment s.1 hp, ih, pow_succ]
    ring

theorem frameCoefficientRow_norm (n : ℕ) (p : ℝ) (s : FrameIndex n)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) :
    ‖frameCoefficientRow n p s‖ = realFrameWitnessScale n p := by
  have hg : 0 ≤ realFrameWitnessScale n p := (Real.exp_pos _).le
  apply (Real.rpow_left_inj (norm_nonneg _) hg hp.ne').mp
  rw [frameCoefficient_norm_rpow n p hp, realFrameWitnessScale_rpow n hp.ne']
  exact normalizedProductFrameRow_moment n s hp

theorem finiteAverage_abs_le {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    |finiteAverage f| ≤ finiteAverage (fun i => |f i|) := by
  unfold finiteAverage
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card ι : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- Finite probability-space Hölder, with the normalization built in. -/
theorem finiteAverage_holder {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    |finiteAverage (fun i => f i * g i)| ≤
      (finiteAverage (fun i => |f i| ^ p)) ^ (1 / p) *
        (finiteAverage (fun i => |g i| ^ q)) ^ (1 / q) := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  have he : 1 - 1 / p = 1 / q := by
    have h := hpq.inv_add_inv_eq_one
    simp only [one_div] at *
    linarith
  have h := finiteAverage_geometric_le (fun i => |f i| ^ p) (fun i => |g i| ^ q)
    (fun i => Real.rpow_nonneg (abs_nonneg _) _)
    (fun i => Real.rpow_nonneg (abs_nonneg _) _) (1 / p) (by positivity)
    (by have := hpq.lt; exact (div_le_one hp).2 (le_of_lt this))
  rw [he] at h
  have hf (i : ι) : (|f i| ^ p) ^ (1 / p) = |f i| := by
    rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one]
  have hg (i : ι) : (|g i| ^ q) ^ (1 / q) = |g i| := by
    rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hq.ne', Real.rpow_one]
  simp only [hf, hg] at h
  exact (finiteAverage_abs_le (fun i => f i * g i)).trans (by simpa only [abs_mul] using h)

theorem frameCoefficientRow_pairing_le (n : ℕ) (p : ℝ) (s : FrameIndex n)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (b : FrameCoefficient n p) :
    |∑ i, b i * normalizedProductFrameRow n s i| ≤
      realFrameWitnessScale n (frameConjugate p) * ‖b‖ := by
  have hpq := frameConjugate_holder hp
  have hq := hpq.symm.pos
  have h := finiteAverage_holder (productFrameEval n b)
    (productFrameEval n (normalizedProductFrameRow n s)) hpq
  rw [productFrameEval_covariance,
    ← frameCoefficient_norm_eq_average n p (by linarith) b,
    normalizedProductFrameRow_moment n s hq,
    ← realFrameWitnessScale_rpow n hq.ne'] at h
  have hg : 0 ≤ realFrameWitnessScale n (frameConjugate p) := (Real.exp_pos _).le
  rw [← Real.rpow_mul hg, mul_one_div_cancel hq.ne', Real.rpow_one] at h
  simpa only [mul_comm] using h

private def frameRowLinear (n : ℕ) (p : ℝ) (s : FrameIndex n) :
    FrameCoefficient n p →ₗ[ℝ] ℝ where
  toFun b := ∑ i, b i * normalizedProductFrameRow n s i
  map_add' b c := by
    change (∑ i, (b i + c i) * normalizedProductFrameRow n s i) = _
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' a b := by
    change (∑ i, (a * b i) * normalizedProductFrameRow n s i) =
      a * ∑ i, b i * normalizedProductFrameRow n s i
    simp only [mul_assoc, Finset.mul_sum]

/-- The actual dual functional associated with the normalized product row. -/
def frameRowFunctional (n : ℕ) (p : ℝ) (s : FrameIndex n)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) : FrameCoefficient n p →L[ℝ] ℝ :=
  (frameRowLinear n p s).mkContinuous (realFrameWitnessScale n (frameConjugate p))
    (fun b => by
      change ‖∑ i, b i * normalizedProductFrameRow n s i‖ ≤ _
      simpa only [Real.norm_eq_abs] using frameCoefficientRow_pairing_le n p s hp b)

@[simp] theorem frameRowFunctional_apply (n : ℕ) (p : ℝ) (s : FrameIndex n)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (b : FrameCoefficient n p) :
    frameRowFunctional n p s hp b = ∑ i, b i * normalizedProductFrameRow n s i := rfl

theorem frameRowFunctional_eq_eval (n : ℕ) (p : ℝ) (s : FrameIndex n)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (b : FrameCoefficient n p) :
    frameRowFunctional n p s hp b =
      (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * productFrameEval n b s := by
  simp only [frameRowFunctional_apply, normalizedProductFrameRow, productFrameEval,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem frameRowFunctional_norm_le (n : ℕ) (p : ℝ) (s : FrameIndex n)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) :
    ‖frameRowFunctional n p s hp‖ ≤ realFrameWitnessScale n (frameConjugate p) := by
  have hg : 0 ≤ realFrameWitnessScale n (frameConjugate p) := (Real.exp_pos _).le
  apply ContinuousLinearMap.opNorm_le_bound _ hg
  intro b
  simpa only [frameRowFunctional_apply, Real.norm_eq_abs] using
    frameCoefficientRow_pairing_le n p s hp b

end ComplementedSubspace
