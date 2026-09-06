import ComplementedSubspace.FiniteSigns
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Finite Hilbert-valued averages depend only on covariance

Equal coordinate covariance implies equal average squared norms under every
linear map to a real inner-product space. This permits replacement of a finite
symmetry orbit by independent signs in the finite-frame trace proof.
-/

noncomputable section

open scoped BigOperators

namespace ComplementedSubspace

variable {ι σ τ H : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [Fintype τ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem linearMap_pi_eq_sum_single (A : (ι → ℝ) →ₗ[ℝ] H) (x : ι → ℝ) :
    A x = ∑ i, x i • A (Pi.single i 1) := by
  classical
  have hx : (∑ i, x i • (Pi.single i 1 : ι → ℝ)) = x := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single x
  calc
    A x = A (∑ i, x i • (Pi.single i 1 : ι → ℝ)) := congrArg A hx.symm
    _ = ∑ i, x i • A (Pi.single i 1) := by simp only [map_sum, map_smul]

/-- The squared norm of a linear image is an explicit quadratic polynomial
in the source coordinates. -/
theorem linearMap_pi_norm_sq (A : (ι → ℝ) →ₗ[ℝ] H) (x : ι → ℝ) :
    ‖A x‖ ^ 2 = ∑ i, ∑ j, (x i * x j) *
      inner ℝ (A (Pi.single i 1)) (A (Pi.single j 1)) := by
  classical
  rw [linearMap_pi_eq_sum_single A x, ← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (A (Pi.single j 1)) (A (Pi.single i 1))]
  ring

/-- Coordinate-covariance expression for a finite Hilbert-valued second moment. -/
theorem finiteAverage_linearMap_norm_sq (x : σ → ι → ℝ)
    (A : (ι → ℝ) →ₗ[ℝ] H) :
    finiteAverage (fun s => ‖A (x s)‖ ^ 2) =
      ∑ i, ∑ j, inner ℝ (A (Pi.single i 1)) (A (Pi.single j 1)) *
        finiteAverage (fun s => x s i * x s j) := by
  classical
  simp only [linearMap_pi_norm_sq, finiteAverage_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa only [mul_comm] using finiteAverage_mul
    (inner ℝ (A (Pi.single i 1)) (A (Pi.single j 1))) (fun s => x s i * x s j)

/-- Replacing a finite sample family by another with the same covariance
preserves every Hilbert-valued second moment. Empty sample sets are permitted
with the existing zero-average convention. -/
theorem finiteAverage_linearMap_norm_sq_eq_of_covariance
    (x : σ → ι → ℝ) (z : τ → ι → ℝ)
    (hcov : ∀ i j, finiteAverage (fun s => x s i * x s j) =
      finiteAverage (fun t => z t i * z t j))
    (A : (ι → ℝ) →ₗ[ℝ] H) :
    finiteAverage (fun s => ‖A (x s)‖ ^ 2) =
      finiteAverage (fun t => ‖A (z t)‖ ^ 2) := by
  simp only [finiteAverage_linearMap_norm_sq, hcov]

end ComplementedSubspace
