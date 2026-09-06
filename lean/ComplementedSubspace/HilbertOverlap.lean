import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hilbert--Schmidt estimates for synthesis operators

This file formalizes the deterministic matrix estimate in the proof of the
fourth-moment lemma in `3-Fourth-moments.tex`.  All displayed matrix norms are
the genuine operator norms for Euclidean spaces.  The Hilbert--Schmidt square
is separately named, to avoid confusing those two norms.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace ComplementedSubspace

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- The square of the Hilbert--Schmidt norm of a real rectangular matrix. -/
def hsSq (A : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, (A i j) ^ 2

lemma hsSq_nonneg (A : Matrix m n ℝ) : 0 ≤ hsSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp]
lemma hsSq_transpose (A : Matrix m n ℝ) : hsSq A.transpose = hsSq A := by
  simp only [hsSq, Matrix.transpose_apply]
  exact Finset.sum_comm

lemma real_opNorm_transpose (A : Matrix m n ℝ) : ‖A.transpose‖ = ‖A‖ := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.l2_opNorm_conjTranspose A

/-- The operator norm controls the Euclidean square of every matrix-vector product. -/
lemma sum_sq_mulVec_le (A : Matrix m n ℝ) (x : n → ℝ) :
    (∑ i, (A.mulVec x i) ^ 2) ≤ ‖A‖ ^ 2 * ∑ j, (x j) ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  change ‖WithLp.toLp 2 (A.mulVec x)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 x‖ at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply] using hsq

/-- Left multiplication is bounded in Hilbert--Schmidt norm by the operator norm. -/
lemma hsSq_mul_le (A : Matrix m n ℝ) (B : Matrix n k ℝ) :
    hsSq (A * B) ≤ ‖A‖ ^ 2 * hsSq B := by
  calc
    hsSq (A * B) = ∑ j, ∑ i, ((A * B) i j) ^ 2 := by
      exact Finset.sum_comm
    _ ≤ ∑ j, ‖A‖ ^ 2 * ∑ i, (B i j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using
        sum_sq_mulVec_le A (fun i => B i j)
    _ = ‖A‖ ^ 2 * hsSq B := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm

/-- Right multiplication satisfies the companion operator/Hilbert--Schmidt estimate. -/
lemma hsSq_mul_right_le (A : Matrix m n ℝ) (B : Matrix n k ℝ) :
    hsSq (A * B) ≤ hsSq A * ‖B‖ ^ 2 := by
  have h := hsSq_mul_le B.transpose A.transpose
  rw [← Matrix.transpose_mul, hsSq_transpose, hsSq_transpose,
    real_opNorm_transpose, mul_comm] at h
  exact h

/-- Discarding the off-diagonal entries can only decrease the Hilbert--Schmidt square. -/
lemma diagonal_sq_le_hsSq (A : Matrix n n ℝ) :
    (∑ i, (A i i) ^ 2) ≤ hsSq A := by
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)

/-- The synthesis-operator diagonal estimate used in the manuscript.

If `B` has columns `bᵢ`, the left hand side is `∑ᵢ ⟨bᵢ, A bᵢ⟩²`.
The bound is independent of both dimensions.
-/
theorem synthesis_diagonal_bound (B : Matrix n k ℝ) (A : Matrix n n ℝ) :
    (∑ i, ((B.transpose * A * B) i i) ^ 2) ≤ ‖B‖ ^ 4 * hsSq A := by
  calc
    _ ≤ hsSq (B.transpose * A * B) := diagonal_sq_le_hsSq _
    _ ≤ hsSq (B.transpose * A) * ‖B‖ ^ 2 := hsSq_mul_right_le _ _
    _ ≤ (‖B.transpose‖ ^ 2 * hsSq A) * ‖B‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hsSq_mul_le _ _) (sq_nonneg _)
    _ = ‖B‖ ^ 4 * hsSq A := by rw [real_opNorm_transpose]; ring

/-- The Hilbert--Schmidt inner product of real matrices. -/
def hsInner (A B : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- The rank-one matrix associated to a real vector. -/
def rankOne (b : n → ℝ) : Matrix n n ℝ := Matrix.vecMulVec b b

lemma hsSq_rankOne (b : n → ℝ) : hsSq (rankOne b) = (∑ j, (b j) ^ 2) ^ 2 := by
  simp only [hsSq, rankOne, Matrix.vecMulVec_apply, mul_pow,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma hsInner_rankOne_eq_diagonal (B : Matrix n k ℝ) (A : Matrix n n ℝ) (i : k) :
    hsInner (rankOne (fun j => B j i)) A = (B.transpose * A * B) i i := by
  simp only [hsInner, rankOne, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The rank-one formulation of the deterministic Hilbert--Schmidt estimate. -/
theorem sum_rankOne_hsInner_sq_le (B : Matrix n k ℝ) (A : Matrix n n ℝ) :
    (∑ i, hsInner (rankOne (fun j => B j i)) A ^ 2) ≤ ‖B‖ ^ 4 * hsSq A := by
  simpa only [hsInner_rankOne_eq_diagonal] using synthesis_diagonal_bound B A

/-- Every column has Euclidean norm at most the synthesis operator norm. -/
lemma column_sq_le_opNorm_sq (B : Matrix n k ℝ) (i : k) :
    (∑ j, (B j i) ^ 2) ≤ ‖B‖ ^ 2 := by
  have h := sum_sq_mulVec_le B (Pi.single i 1)
  simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using h

/-- Passing a rank-one Hilbert--Schmidt estimate to an arbitrary column family.

In the manuscript `D` is the tensor power of the circle-moment map and
`r = (5/8)^n`.  That specialized estimate is an explicit hypothesis here;
the theorem proves the subsequent dimension-free synthesis-operator step.
Neither positivity nor linearity of `D` is required for this step.
-/
theorem column_moments_bound (B : Matrix n k ℝ)
    (D : Matrix n n ℝ → Matrix n n ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hD : ∀ b : n → ℝ, hsSq (D (rankOne b)) ≤ r * (∑ j, (b j) ^ 2) ^ 2) :
    (∑ i, ∑ j,
      hsInner (rankOne (fun l => B l i)) (D (rankOne (fun l => B l j))) ^ 2) ≤
      (Fintype.card k : ℝ) * ‖B‖ ^ 8 * r := by
  have hcol (j : k) : (∑ l, (B l j) ^ 2) ^ 2 ≤ ‖B‖ ^ 4 := by
    have h := pow_le_pow_left₀
      (Finset.sum_nonneg fun l _ => sq_nonneg (B l j)) (column_sq_le_opNorm_sq B j) 2
    simpa only [← pow_mul] using h
  calc
    _ = ∑ j, ∑ i,
        hsInner (rankOne (fun l => B l i)) (D (rankOne (fun l => B l j))) ^ 2 :=
      Finset.sum_comm
    _ ≤ ∑ j : k, ‖B‖ ^ 4 * (r * ‖B‖ ^ 4) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖B‖ ^ 4 * hsSq (D (rankOne (fun l => B l j))) :=
          sum_rankOne_hsInner_sq_le B _
        _ ≤ ‖B‖ ^ 4 * (r * (∑ l, (B l j) ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (hD _) (pow_nonneg (norm_nonneg _) _)
        _ ≤ ‖B‖ ^ 4 * (r * ‖B‖ ^ 4) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcol j) hr)
            (pow_nonneg (norm_nonneg _) _)
    _ = (Fintype.card k : ℝ) * ‖B‖ ^ 8 * r := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The Cauchy--Schwarz step combining the two synthesis families.

Together with the separate probabilistic moment identity and the specialized
rank-one bound, this is the deterministic conclusion of the fourth-moment proof.
-/
theorem paired_column_moments_bound (B V : Matrix n k ℝ)
    (D : Matrix n n ℝ → Matrix n n ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hD : ∀ b : n → ℝ, hsSq (D (rankOne b)) ≤ r * (∑ j, (b j) ^ 2) ^ 2) :
    (∑ i, ∑ j,
      hsInner (rankOne (fun l => B l i)) (D (rankOne (fun l => B l j))) *
      hsInner (rankOne (fun l => V l i)) (D (rankOne (fun l => V l j)))) ≤
      (Fintype.card k : ℝ) * (‖B‖ * ‖V‖) ^ 4 * r := by
  let f : k × k → ℝ := fun p =>
    hsInner (rankOne (fun l => B l p.1)) (D (rankOne (fun l => B l p.2)))
  let g : k × k → ℝ := fun p =>
    hsInner (rankOne (fun l => V l p.1)) (D (rankOne (fun l => V l p.2)))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hb : (∑ p, f p ^ 2) ≤ (Fintype.card k : ℝ) * ‖B‖ ^ 8 * r := by
    simpa only [Fintype.sum_prod_type, f] using column_moments_bound B D r hr hD
  have hv : (∑ p, g p ^ 2) ≤ (Fintype.card k : ℝ) * ‖V‖ ^ 8 * r := by
    simpa only [Fintype.sum_prod_type, g] using column_moments_bound V D r hr hD
  have hprod : (∑ p, f p ^ 2) * (∑ p, g p ^ 2) ≤
      ((Fintype.card k : ℝ) * (‖B‖ * ‖V‖) ^ 4 * r) ^ 2 := by
    calc
      _ ≤ ((Fintype.card k : ℝ) * ‖B‖ ^ 8 * r) *
          ((Fintype.card k : ℝ) * ‖V‖ ^ 8 * r) :=
        mul_le_mul hb hv (Finset.sum_nonneg fun p _ => sq_nonneg (g p)) (by positivity)
      _ = _ := by ring
  have hfinal := le_of_sq_le_sq (hcs.trans hprod)
    (show 0 ≤ (Fintype.card k : ℝ) * (‖B‖ * ‖V‖) ^ 4 * r by positivity)
  simpa only [Fintype.sum_prod_type, f, g] using hfinal

/-- The real two-dimensional circle-moment map from the manuscript. -/
def circleMomentMap (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 4 : ℝ) • (A.trace • (1 : Matrix (Fin 2) (Fin 2) ℝ) + A + A.transpose)

/-- The circle-moment map is self-adjoint for the Hilbert--Schmidt inner product. -/
theorem circleMomentMap_hs_selfAdjoint (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    hsInner (circleMomentMap A) B = hsInner A (circleMomentMap B) := by
  simp [hsInner, circleMomentMap, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.smul_apply, Matrix.transpose_apply]
  ring

/-- Exact rank-one Hilbert--Schmidt computation for a single circle factor.

This proves the `n = 1` case of the manuscript's rank-one moment estimate.
The extension to arbitrary tensor powers requires additional mathematics.
-/
theorem circleMomentMap_rankOne_hsSq (b : Fin 2 → ℝ) :
    hsSq (circleMomentMap (rankOne b)) = (5 / 8 : ℝ) * (∑ j, (b j) ^ 2) ^ 2 := by
  simp [hsSq, circleMomentMap, rankOne, Matrix.vecMulVec_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two, Matrix.one_apply, Matrix.smul_apply,
    Matrix.transpose_apply]
  ring

/-- The manuscript's column-moment estimate for a single circle factor,
with no additional mathematical hypotheses. -/
theorem circle_column_moments_bound (B : Matrix (Fin 2) k ℝ) :
    (∑ i, ∑ j,
      hsInner (rankOne (fun l => B l i))
        (circleMomentMap (rankOne (fun l => B l j))) ^ 2) ≤
      (Fintype.card k : ℝ) * ‖B‖ ^ 8 * (5 / 8 : ℝ) :=
  column_moments_bound B circleMomentMap (5 / 8) (by positivity)
    (fun b => (circleMomentMap_rankOne_hsSq b).le)

/-- The paired-column fourth-moment estimate for one circle factor. -/
theorem circle_paired_column_moments_bound (B V : Matrix (Fin 2) k ℝ) :
    (∑ i, ∑ j,
      hsInner (rankOne (fun l => B l i))
        (circleMomentMap (rankOne (fun l => B l j))) *
      hsInner (rankOne (fun l => V l i))
        (circleMomentMap (rankOne (fun l => V l j)))) ≤
      (Fintype.card k : ℝ) * (‖B‖ * ‖V‖) ^ 4 * (5 / 8 : ℝ) :=
  paired_column_moments_bound B V circleMomentMap (5 / 8) (by positivity)
    (fun b => (circleMomentMap_rankOne_hsSq b).le)

end ComplementedSubspace
