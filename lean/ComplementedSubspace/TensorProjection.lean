import ComplementedSubspace.FrameProjectionNorm
import ComplementedSubspace.ProductFrameIndex
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Tensor projection bounds by finite coordinate slices, for counting `ℓᵖ` norms. -/

noncomputable section
open scoped BigOperators ENNReal Kronecker
open Matrix WithLp

namespace ComplementedSubspace

lemma kronecker_mulVec_slice {ι κ μ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    (A : Matrix κ ι ℝ) (B : Matrix ν μ ℝ) (x : ι × μ → ℝ) (i : κ) (j : ν) :
    ((A ⊗ₖ B) *ᵥ x) (i, j) =
      (A *ᵥ fun a => (B *ᵥ fun b => x (a, b)) j) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Finset.mul_sum, mul_assoc]

lemma finitePEnergy_kronecker_le {ι κ μ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    {p C D : ℝ} (hC : 0 ≤ C)
    (A : Matrix κ ι ℝ) (B : Matrix ν μ ℝ)
    (hA : ∀ x, finitePEnergy p (A *ᵥ x) ≤ C * finitePEnergy p x)
    (hB : ∀ x, finitePEnergy p (B *ᵥ x) ≤ D * finitePEnergy p x)
    (x : ι × μ → ℝ) :
    finitePEnergy p ((A ⊗ₖ B) *ᵥ x) ≤ (C * D) * finitePEnergy p x := by
  calc
    finitePEnergy p ((A ⊗ₖ B) *ᵥ x) =
        ∑ j, finitePEnergy p (A *ᵥ fun a => (B *ᵥ fun b => x (a, b)) j) := by
      simp only [finitePEnergy, Fintype.sum_prod_type, kronecker_mulVec_slice]
      exact Finset.sum_comm
    _ ≤ ∑ j, C * finitePEnergy p (fun a => (B *ᵥ fun b => x (a, b)) j) :=
      Finset.sum_le_sum fun j _ => hA _
    _ = C * ∑ a, finitePEnergy p (B *ᵥ fun b => x (a, b)) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    _ ≤ C * ∑ a, D * finitePEnergy p (fun b => x (a, b)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum fun a _ => hB _
    _ = (C * D) * finitePEnergy p x := by
      simp only [finitePEnergy, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

lemma finitePEnergy_matrix_le_opNorm {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (M : Matrix κ ι ℝ) (x : ι → ℝ) :
    finitePEnergy p (M *ᵥ x) ≤
      ‖matrixPiLpCLM (ENNReal.ofReal p) M‖ ^ p * finitePEnergy p x := by
  have h := (matrixPiLpCLM (ENNReal.ofReal p) M).le_opNorm
    (toLp (ENNReal.ofReal p) x)
  have hr := Real.rpow_le_rpow (norm_nonneg _) h hp.le
  rw [matrixPiLpCLM_apply, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    norm_toLp_rpow hp, norm_toLp_rpow hp] at hr
  exact hr

theorem matrixPiLpCLM_kronecker_norm_le {ι κ μ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (A : Matrix κ ι ℝ) (B : Matrix ν μ ℝ) :
    ‖matrixPiLpCLM (ENNReal.ofReal p) (A ⊗ₖ B)‖ ≤
      ‖matrixPiLpCLM (ENNReal.ofReal p) A‖ * ‖matrixPiLpCLM (ENNReal.ofReal p) B‖ := by
  apply matrixPiLpCLM_norm_le_of_energy hp (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact finitePEnergy_kronecker_le
    (Real.rpow_nonneg (norm_nonneg _) p) A B
    (finitePEnergy_matrix_le_opNorm hp A) (finitePEnergy_matrix_le_opNorm hp B) x

/-- Exact Kronecker powers of the four-point orthogonal frame projector. -/
def tensorFrameProjection : (n : ℕ) → Matrix (FrameIndex n) (FrameIndex n) ℝ
  | 0 => 1
  | n + 1 => realFrameProjection ⊗ₖ tensorFrameProjection n

lemma realFrameProjection_diag (i : Fin 4) : realFrameProjection i i = (1 / 2 : ℝ) := by
  change (1 / 4 : ℝ) * (∑ j, realFrame i j * realFrame i j) = 1 / 2
  simp only [← pow_two, realFrame_length_sq]
  norm_num

theorem tensorFrameProjection_diag (n : ℕ) (i : FrameIndex n) :
    tensorFrameProjection n i i = (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp [tensorFrameProjection]
  | succ n ih =>
    change realFrameProjection i.1 i.1 * tensorFrameProjection n i.2 i.2 = _
    rw [realFrameProjection_diag, ih, pow_succ]
    ring

theorem tensorFrameProjection_ne_zero (n : ℕ) : tensorFrameProjection n ≠ 0 := by
  intro h
  have hd := tensorFrameProjection_diag n (Classical.choice (frameIndexNonempty n))
  rw [h, Matrix.zero_apply] at hd
  exact pow_ne_zero n (by norm_num : (1 / 2 : ℝ) ≠ 0) hd.symm

theorem tensorFrameProjection_ne_one {n : ℕ} (hn : n ≠ 0) :
    tensorFrameProjection n ≠ 1 := by
  intro h
  have hd := tensorFrameProjection_diag n (Classical.choice (frameIndexNonempty n))
  rw [h, Matrix.one_apply_eq] at hd
  have hl := pow_lt_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hn
  linarith

theorem tensorFrameProjection_idempotent (n : ℕ) :
    tensorFrameProjection n * tensorFrameProjection n = tensorFrameProjection n := by
  induction n with
  | zero => simp [tensorFrameProjection]
  | succ n ih =>
    change (realFrameProjection ⊗ₖ tensorFrameProjection n) *
      (realFrameProjection ⊗ₖ tensorFrameProjection n) = _
    rw [← Matrix.mul_kronecker_mul, realFrameProjection_idempotent, ih]
    rfl

theorem tensorFrameProjection_transpose (n : ℕ) :
    (tensorFrameProjection n).transpose = tensorFrameProjection n := by
  induction n with
  | zero => simp [tensorFrameProjection]
  | succ n ih =>
    change (realFrameProjection ⊗ₖ tensorFrameProjection n).transpose = _
    rw [← Matrix.kroneckerMap_transpose, realFrameProjection_transpose, ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem tensorFrameProjection_energy_bound {p : ℝ} (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (n : ℕ) (x : FrameIndex n → ℝ) :
    finitePEnergy p (tensorFrameProjection n *ᵥ x) ≤
      (1 + 18 * (p - 2) ^ 2) ^ n * finitePEnergy p x := by
  induction n with
  | zero => simp [tensorFrameProjection]
  | succ n ih =>
    have h := finitePEnergy_kronecker_le (p := p)
      (by positivity : 0 ≤ 1 + 18 * (p - 2) ^ 2)
      realFrameProjection (tensorFrameProjection n)
      (fin_four_matrix_energy_bound hp hp3 realFrameProjection
        realFrameProjection_transpose realFrameProjection_idempotent)
      ih x
    rw [pow_succ' (1 + 18 * (p - 2) ^ 2) n]
    exact h

theorem tensorFrameProjection_norm_le {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hp3 : p ≤ 3) (n : ℕ) :
    ‖matrixPiLpCLM (ENNReal.ofReal p) (tensorFrameProjection n)‖ ≤
      (1 + 18 * (p - 2) ^ 2) ^ n := by
  have hC : 1 ≤ (1 + 18 * (p - 2) ^ 2) ^ n :=
    one_le_pow₀ (by nlinarith [sq_nonneg (p - 2)])
  apply matrixPiLpCLM_norm_le_of_energy (by linarith : 0 < p) (by positivity)
  intro x
  exact (tensorFrameProjection_energy_bound hp hp3 n x).trans
    (mul_le_mul_of_nonneg_right
      (Real.self_le_rpow_of_one_le hC (by linarith)) (finitePEnergy_nonneg p x))

theorem tensorFrameProjection_clm_idempotent (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    (matrixPiLpCLM p (tensorFrameProjection n)).comp
      (matrixPiLpCLM p (tensorFrameProjection n)) =
        matrixPiLpCLM p (tensorFrameProjection n) :=
  matrixPiLpCLM_idempotent p _ (tensorFrameProjection_idempotent n)

theorem tensorFrameProjection_norm_le_exp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hp3 : p ≤ 3) (n : ℕ) :
    ‖matrixPiLpCLM (ENNReal.ofReal p) (tensorFrameProjection n)‖ ≤
      Real.exp (18 * (n : ℝ) * (p - 2) ^ 2) := by
  refine (tensorFrameProjection_norm_le hp hp3 n).trans ?_
  calc
    (1 + 18 * (p - 2) ^ 2) ^ n ≤ (Real.exp (18 * (p - 2) ^ 2)) ^ n := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (18 * (p - 2) ^ 2)
    _ = Real.exp (18 * (n : ℝ) * (p - 2) ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem one_le_tensorFrameProjection_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    1 ≤ ‖matrixPiLpCLM p (tensorFrameProjection n)‖ := by
  have hP : matrixPiLpCLM p (tensorFrameProjection n) ≠ 0 :=
    matrixPiLpCLM_ne_zero p _ (tensorFrameProjection_ne_zero n)
  have hnorm := (matrixPiLpCLM p (tensorFrameProjection n)).opNorm_comp_le
    (matrixPiLpCLM p (tensorFrameProjection n))
  rw [tensorFrameProjection_clm_idempotent] at hnorm
  have hpos := norm_pos_iff.mpr hP
  nlinarith

theorem tensorFrameProjection_norm_tendsto_one {ι : Type*} {l : Filter ι}
    (p : ι → ℝ) (n : ι → ℕ) [∀ i, Fact (1 ≤ ENNReal.ofReal (p i))]
    (hp : ∀ i, 2 ≤ p i) (hp3 : ∀ i, p i ≤ 3)
    (heps : Filter.Tendsto (fun i => (n i : ℝ) * (p i - 2) ^ 2) l (nhds 0)) :
    Filter.Tendsto
      (fun i => ‖matrixPiLpCLM (ENNReal.ofReal (p i)) (tensorFrameProjection (n i))‖)
      l (nhds 1) := by
  have hlim : Filter.Tendsto (fun i => Real.exp (18 * (n i : ℝ) * (p i - 2) ^ 2))
      l (nhds 1) := by
    simpa only [mul_zero, Real.exp_zero, mul_assoc, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp (heps.const_mul 18)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun i => one_le_tensorFrameProjection_norm _ _)
    (fun i => tensorFrameProjection_norm_le_exp (hp i) (hp3 i) (n i))

end ComplementedSubspace
