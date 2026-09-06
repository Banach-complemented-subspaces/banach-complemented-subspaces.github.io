import ComplementedSubspace.ComplexFrameProjection
import ComplementedSubspace.TensorProjection

/-! Complex tensor powers of the same real finite orthogonal projection.
Norm estimates use complex coordinate slices with no loss in constants. -/
noncomputable section
open scoped BigOperators ENNReal Kronecker
open Matrix WithLp
namespace ComplementedSubspace
lemma complexKronecker_mulVec_slice {ι κ μ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    (A : Matrix κ ι ℂ) (B : Matrix ν μ ℂ) (x : ι × μ → ℂ) (i : κ) (j : ν) :
    ((A ⊗ₖ B) *ᵥ x) (i, j) =
      (A *ᵥ fun a => (B *ᵥ fun b => x (a, b)) j) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Finset.mul_sum, mul_assoc]

lemma complexPEnergy_kronecker_le {ι κ μ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    {p C D : ℝ} (hC : 0 ≤ C)
    (A : Matrix κ ι ℂ) (B : Matrix ν μ ℂ)
    (hA : ∀ x, complexPEnergy p (A *ᵥ x) ≤ C * complexPEnergy p x)
    (hB : ∀ x, complexPEnergy p (B *ᵥ x) ≤ D * complexPEnergy p x)
    (x : ι × μ → ℂ) :
    complexPEnergy p ((A ⊗ₖ B) *ᵥ x) ≤ (C * D) * complexPEnergy p x := by
  calc
    complexPEnergy p ((A ⊗ₖ B) *ᵥ x) =
        ∑ j, complexPEnergy p (A *ᵥ fun a => (B *ᵥ fun b => x (a, b)) j) := by
      simp only [complexPEnergy, Fintype.sum_prod_type, complexKronecker_mulVec_slice]
      exact Finset.sum_comm
    _ ≤ ∑ j, C * complexPEnergy p (fun a => (B *ᵥ fun b => x (a, b)) j) :=
      Finset.sum_le_sum fun j _ => hA _
    _ = C * ∑ a, complexPEnergy p (B *ᵥ fun b => x (a, b)) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    _ ≤ C * ∑ a, D * complexPEnergy p (fun b => x (a, b)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum fun a _ => hB _
    _ = (C * D) * complexPEnergy p x := by
      simp only [complexPEnergy, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

lemma complexPEnergy_matrix_le_opNorm {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (M : Matrix κ ι ℂ) (x : ι → ℂ) :
    complexPEnergy p (M *ᵥ x) ≤
      ‖complexMatrixPiLpCLM (ENNReal.ofReal p) M‖ ^ p * complexPEnergy p x := by
  have h := (complexMatrixPiLpCLM (ENNReal.ofReal p) M).le_opNorm
    (toLp (ENNReal.ofReal p) x)
  have hr := Real.rpow_le_rpow (norm_nonneg _) h hp.le
  rw [complexMatrixPiLpCLM_apply, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    complex_norm_toLp_rpow hp, complex_norm_toLp_rpow hp] at hr
  exact hr

theorem complexMatrixPiLpCLM_kronecker_norm_le {ι κ μ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (A : Matrix κ ι ℂ) (B : Matrix ν μ ℂ) :
    ‖complexMatrixPiLpCLM (ENNReal.ofReal p) (A ⊗ₖ B)‖ ≤
      ‖complexMatrixPiLpCLM (ENNReal.ofReal p) A‖ * ‖complexMatrixPiLpCLM (ENNReal.ofReal p) B‖ := by
  apply complexMatrixPiLpCLM_norm_le_of_energy hp (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact complexPEnergy_kronecker_le
    (Real.rpow_nonneg (norm_nonneg _) p) A B
    (complexPEnergy_matrix_le_opNorm hp A) (complexPEnergy_matrix_le_opNorm hp B) x

def complexTensorFrameProjection (n : ℕ) : Matrix (FrameIndex n) (FrameIndex n) ℂ :=
  complexifyMatrix (tensorFrameProjection n)

@[simp] theorem complexTensorFrameProjection_zero : complexTensorFrameProjection 0 = 1 := by
  classical
  ext i j
  by_cases h : i = j <;>
    simp [complexTensorFrameProjection, complexifyMatrix, tensorFrameProjection, Matrix.one_apply, h]

theorem complexTensorFrameProjection_succ (n : ℕ) :
    complexTensorFrameProjection (n + 1) = complexFrameProjection ⊗ₖ complexTensorFrameProjection n := by
  ext i j
  change ((realFrameProjection i.1 j.1 * tensorFrameProjection n i.2 j.2 : ℝ) : ℂ) =
    (realFrameProjection i.1 j.1 : ℂ) * (tensorFrameProjection n i.2 j.2 : ℂ)
  exact Complex.ofReal_mul _ _

theorem complexTensorFrameProjection_idempotent (n : ℕ) :
    complexTensorFrameProjection n * complexTensorFrameProjection n = complexTensorFrameProjection n :=
  complexifyMatrix_idempotent _ (tensorFrameProjection_idempotent n)

theorem complexTensorFrameProjection_ne_zero (n : ℕ) : complexTensorFrameProjection n ≠ 0 := by
  intro h
  apply tensorFrameProjection_ne_zero n
  ext i j
  have hij := congrArg (fun M : Matrix (FrameIndex n) (FrameIndex n) ℂ => (M i j).re) h
  simpa [complexTensorFrameProjection, complexifyMatrix] using hij

theorem complexTensorFrameProjection_energy_bound {p : ℝ} (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (n : ℕ) (x : FrameIndex n → ℂ) :
    complexPEnergy p (complexTensorFrameProjection n *ᵥ x) ≤
      (1 + 18 * (p - 2) ^ 2) ^ n * complexPEnergy p x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [complexTensorFrameProjection_succ, pow_succ']
    exact complexPEnergy_kronecker_le (p := p)
      (by positivity : 0 ≤ 1 + 18 * (p - 2) ^ 2)
      complexFrameProjection (complexTensorFrameProjection n)
      (fin_four_complex_matrix_energy_bound hp hp3 realFrameProjection
        realFrameProjection_transpose realFrameProjection_idempotent) ih x

theorem complexTensorFrameProjection_norm_le {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hp3 : p ≤ 3) (n : ℕ) :
    ‖complexMatrixPiLpCLM (ENNReal.ofReal p) (complexTensorFrameProjection n)‖ ≤
      (1 + 18 * (p - 2) ^ 2) ^ n := by
  have hC : 1 ≤ (1 + 18 * (p - 2) ^ 2) ^ n :=
    one_le_pow₀ (by nlinarith [sq_nonneg (p - 2)])
  apply complexMatrixPiLpCLM_norm_le_of_energy (by linarith : 0 < p) (by positivity)
  intro x
  exact (complexTensorFrameProjection_energy_bound hp hp3 n x).trans
    (mul_le_mul_of_nonneg_right
      (Real.self_le_rpow_of_one_le hC (by linarith)) (complexPEnergy_nonneg p x))

theorem complexTensorFrameProjection_clm_idempotent (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    (complexMatrixPiLpCLM p (complexTensorFrameProjection n)).comp
      (complexMatrixPiLpCLM p (complexTensorFrameProjection n)) =
        complexMatrixPiLpCLM p (complexTensorFrameProjection n) :=
  complexMatrixPiLpCLM_idempotent p _ (complexTensorFrameProjection_idempotent n)

theorem complexTensorFrameProjection_norm_le_exp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hp3 : p ≤ 3) (n : ℕ) :
    ‖complexMatrixPiLpCLM (ENNReal.ofReal p) (complexTensorFrameProjection n)‖ ≤
      Real.exp (18 * (n : ℝ) * (p - 2) ^ 2) := by
  refine (complexTensorFrameProjection_norm_le hp hp3 n).trans ?_
  calc
    (1 + 18 * (p - 2) ^ 2) ^ n ≤ (Real.exp (18 * (p - 2) ^ 2)) ^ n := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (18 * (p - 2) ^ 2)
    _ = Real.exp (18 * (n : ℝ) * (p - 2) ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem one_le_complexTensorFrameProjection_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    1 ≤ ‖complexMatrixPiLpCLM p (complexTensorFrameProjection n)‖ := by
  have hP : complexMatrixPiLpCLM p (complexTensorFrameProjection n) ≠ 0 :=
    complexMatrixPiLpCLM_ne_zero p _ (complexTensorFrameProjection_ne_zero n)
  have hnorm := (complexMatrixPiLpCLM p (complexTensorFrameProjection n)).opNorm_comp_le
    (complexMatrixPiLpCLM p (complexTensorFrameProjection n))
  rw [complexTensorFrameProjection_clm_idempotent] at hnorm
  have hpos := norm_pos_iff.mpr hP
  nlinarith

theorem complexTensorFrameProjection_norm_tendsto_one {ι : Type*} {l : Filter ι}
    (p : ι → ℝ) (n : ι → ℕ) [∀ i, Fact (1 ≤ ENNReal.ofReal (p i))]
    (hp : ∀ i, 2 ≤ p i) (hp3 : ∀ i, p i ≤ 3)
    (heps : Filter.Tendsto (fun i => (n i : ℝ) * (p i - 2) ^ 2) l (nhds 0)) :
    Filter.Tendsto
      (fun i => ‖complexMatrixPiLpCLM (ENNReal.ofReal (p i)) (complexTensorFrameProjection (n i))‖)
      l (nhds 1) := by
  have hlim : Filter.Tendsto (fun i => Real.exp (18 * (n i : ℝ) * (p i - 2) ^ 2))
      l (nhds 1) := by
    simpa only [mul_zero, Real.exp_zero, mul_assoc, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp (heps.const_mul 18)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun i => one_le_complexTensorFrameProjection_norm _ _)
    (fun i => complexTensorFrameProjection_norm_le_exp (hp i) (hp3 i) (n i))

end ComplementedSubspace


