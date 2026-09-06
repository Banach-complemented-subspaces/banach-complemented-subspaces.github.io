import ComplementedSubspace.HilbertOverlap
import Mathlib.Tactic.FinCases

/-! A finite replacement for the real circle's second and fourth moments.
The four vectors have Euclidean norm sqrt 2. All averages below are finite
sums with uniform weights. No continuous probability measure is involved. -/

noncomputable section
namespace ComplementedSubspace
open Matrix

def realFrame : Matrix (Fin 4) (Fin 2) ℝ :=
  ![![Real.sqrt 2, 0], ![0, Real.sqrt 2], ![1, 1], ![1, -1]]

theorem realFrame_length_sq (i : Fin 4) :
    (∑ j, (realFrame i j) ^ 2) = 2 := by
  fin_cases i <;> norm_num [realFrame, Fin.sum_univ_two, Real.sq_sqrt]

theorem realFrame_covariance :
    (1 / 4 : ℝ) • (∑ i : Fin 4, rankOne (realFrame i)) = 1 := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    norm_num [realFrame, rankOne, Matrix.vecMulVec_apply,
      Fin.sum_univ_succ, Matrix.one_apply, Real.mul_self_sqrt]

/-- The finite frame has exactly the circle's fourth-moment map.
Since the frame vectors have length sqrt 2, their averaged rank-one
sandwich is twice `circleMomentMap`. -/
theorem realFrame_fourth_moment (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (1 / 4 : ℝ) • (∑ i : Fin 4,
      rankOne (realFrame i) * A * rankOne (realFrame i)) =
      2 • circleMomentMap A := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [realFrame, rankOne,
      Fin.sum_univ_succ, Matrix.mul_apply,
      circleMomentMap, Matrix.trace, Matrix.diag, Real.mul_self_sqrt] <;> ring

/-- The projection onto the two-dimensional frame coefficient space. -/
def realFrameProjection : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 4 : ℝ) • (realFrame * realFrame.transpose)

theorem realFrame_gram : realFrame.transpose * realFrame = (4 : ℝ) • 1 := by
  ext j k
  change (∑ i : Fin 4, realFrame i j * realFrame i k) =
    4 * (1 : Matrix (Fin 2) (Fin 2) ℝ) j k
  fin_cases j <;> fin_cases k <;>
    norm_num [realFrame, Fin.sum_univ_succ,
      Matrix.one_apply, Real.mul_self_sqrt]

theorem realFrameProjection_idempotent :
    realFrameProjection * realFrameProjection = realFrameProjection := by
  unfold realFrameProjection
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc realFrame.transpose,
    realFrame_gram, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul]
  norm_num

theorem realFrameProjection_transpose :
    realFrameProjection.transpose = realFrameProjection := by
  simp [realFrameProjection, Matrix.transpose_mul]

end ComplementedSubspace
