import ComplementedSubspace.GLRetraction
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Gordon--Lewis bounds for the dual of a complemented subspace

Taking adjoints reverses a retraction. The operator norm of each adjoint is
bounded by that of its original map, which suffices for the sharp projection
estimate. No identification of the dual of an infinite sum is used.
-/

noncomputable section
open scoped ENNReal NNReal

namespace ComplementedSubspace

variable {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Precomposition as the bounded map on strong duals. -/
def dualPullback (T : X →L[ℝ] Z) : StrongDual ℝ Z →L[ℝ] StrongDual ℝ X :=
  ContinuousLinearMap.precomp ℝ T

@[simp]
theorem dualPullback_apply (T : X →L[ℝ] Z) (φ : StrongDual ℝ Z) (x : X) :
    dualPullback T φ x = φ (T x) := rfl

theorem norm_dualPullback_le (T : X →L[ℝ] Z) : ‖dualPullback T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro φ
  change ‖φ.comp T‖ ≤ ‖T‖ * ‖φ‖
  simpa only [mul_comm] using φ.opNorm_comp_le T

theorem enorm_dualPullback_le (T : X →L[ℝ] Z) : ‖dualPullback T‖ₑ ≤ ‖T‖ₑ :=
  enorm_le_iff_norm_le.mpr (norm_dualPullback_le T)

/-- The empty supremum convention gives GL constant zero for the zero space. -/
theorem chiGL_eq_zero_of_subsingleton [Subsingleton X] : chiGL X = 0 := by
  apply le_antisymm _ (zero_le)
  refine iSup_le fun V => iSup_le fun _ => iSup_le fun hV => ?_
  exact (hV (Submodule.eq_bot_of_subsingleton (p := V))).elim

theorem dualPullback_retraction (J : Z →L[ℝ] X) (R : X →L[ℝ] Z)
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ Z) :
    (dualPullback J).comp (dualPullback R) =
      ContinuousLinearMap.id ℝ (StrongDual ℝ Z) := by
  ext φ z
  change φ (R (J z)) = φ z
  have hz : R (J z) = z :=
    congrArg (fun T : Z →L[ℝ] Z => T z) hRJ
  rw [hz]

/-- The dual of a bounded retract inherits the quantitative GL bound. -/
theorem chiGL_dual_le_of_retraction (J : Z →L[ℝ] X) (R : X →L[ℝ] Z)
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ Z) :
    chiGL (StrongDual ℝ Z) ≤ ‖R‖ₑ * ‖J‖ₑ * chiGL (StrongDual ℝ X) := by
  rcases subsingleton_or_nontrivial (StrongDual ℝ Z) with hZ | hZ
  · letI := hZ
    rw [chiGL_eq_zero_of_subsingleton]
    exact zero_le
  · letI := hZ
    exact (chiGL_le_of_retraction (dualPullback R) (dualPullback J)
      (dualPullback_retraction J R hRJ)).trans
      (mul_le_mul' (mul_le_mul' (enorm_dualPullback_le R)
        (enorm_dualPullback_le J)) le_rfl)

theorem chiGL_dual_le_norm_product_of_retraction
    (J : Z →L[ℝ] X) (R : X →L[ℝ] Z)
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ Z)
    (hX : chiGL (StrongDual ℝ X) ≤ 1) :
    chiGL (StrongDual ℝ Z) ≤ ‖R‖ₑ * ‖J‖ₑ := by
  calc
    chiGL (StrongDual ℝ Z) ≤ ‖R‖ₑ * ‖J‖ₑ * chiGL (StrongDual ℝ X) :=
      chiGL_dual_le_of_retraction J R hRJ
    _ ≤ ‖R‖ₑ * ‖J‖ₑ * 1 := mul_le_mul' le_rfl hX
    _ = ‖R‖ₑ * ‖J‖ₑ := mul_one _

/-- The dual of the range of a projection has GL constant bounded by the
projection norm whenever the ambient dual has GL constant at most one.
The zero projection is included. -/
theorem chiGL_dual_range_le_projection_norm (P : X →L[ℝ] X)
    (hP : P.comp P = P) (hX : chiGL (StrongDual ℝ X) ≤ 1) :
    chiGL (StrongDual ℝ ↥P.range) ≤ ‖P‖ₑ := by
  have h := chiGL_dual_le_norm_product_of_retraction P.range.subtypeL P.rangeRestrict
    (projection_range_retraction P hP) hX
  have hinc : ‖P.range.subtypeL‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [Submodule.subtypeL_apply, Submodule.norm_coe, one_mul, le_refl]
  have hincE : ‖P.range.subtypeL‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hinc
  have hres : ‖P.rangeRestrict‖ₑ = ‖P‖ₑ :=
    enorm_eq_iff_norm_eq.mpr (norm_rangeRestrict P)
  calc
    chiGL (StrongDual ℝ ↥P.range) ≤ ‖P.rangeRestrict‖ₑ * ‖P.range.subtypeL‖ₑ := h
    _ ≤ ‖P‖ₑ * 1 := mul_le_mul' (le_of_eq hres) hincE
    _ = ‖P‖ₑ := mul_one _

end ComplementedSubspace

