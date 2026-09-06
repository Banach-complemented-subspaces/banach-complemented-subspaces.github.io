import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import ComplementedSubspace.GLDualRetraction

/-!
The actual finite-dimensional bidual isometry. The short norm argument follows
Mathlib.Analysis.Normed.Module.DoubleDual (Heather Macbeth and Michał Świętek,
Apache 2.0); reproducing only that argument avoids unrelated weak-star imports.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
namespace ComplementedSubspace

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def realBidualEvaluation : E →L[ℝ] StrongDual ℝ (StrongDual ℝ E) :=
  ContinuousLinearMap.apply ℝ ℝ

@[simp] theorem realBidualEvaluation_apply (x : E) (f : StrongDual ℝ E) :
    realBidualEvaluation E x f = f x := rfl

def realBidualEvaluationIsometry : E →ₗᵢ[ℝ] StrongDual ℝ (StrongDual ℝ E) :=
  { realBidualEvaluation E with
    norm_map' x := by
      change ‖realBidualEvaluation E x‖ = ‖x‖
      apply le_antisymm
      · apply ContinuousLinearMap.opNorm_le_bound (realBidualEvaluation E x) (norm_nonneg x)
        intro f
        change ‖f x‖ ≤ ‖x‖ * ‖f‖
        simpa only [mul_comm] using f.le_opNorm x
      · obtain ⟨g, hg⟩ := exists_dual_vector'' ℝ x
        have h := (realBidualEvaluation E x).unit_le_opNorm g hg.left
        simpa [hg.right] using h }

theorem finiteStrongDual_finrank [FiniteDimensional ℝ E] :
    Module.finrank ℝ (StrongDual ℝ E) = Module.finrank ℝ E := by
  calc
    _ = Module.finrank ℝ (Module.Dual ℝ E) :=
      (LinearMap.toContinuousLinearMap : Module.Dual ℝ E ≃ₗ[ℝ] StrongDual ℝ E).finrank_eq.symm
    _ = _ := Subspace.dual_finrank_eq

def finiteBidualEquiv [FiniteDimensional ℝ E] :
    E ≃ₗᵢ[ℝ] StrongDual ℝ (StrongDual ℝ E) :=
  (realBidualEvaluationIsometry E).toLinearIsometryEquiv (by
    rw [finiteStrongDual_finrank, finiteStrongDual_finrank])

@[simp] theorem finiteBidualEquiv_apply [FiniteDimensional ℝ E]
    (x : E) (f : StrongDual ℝ E) : finiteBidualEquiv E x f = f x := rfl

end ComplementedSubspace
