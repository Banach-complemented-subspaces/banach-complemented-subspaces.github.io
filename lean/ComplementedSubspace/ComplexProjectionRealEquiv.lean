import ComplementedSubspace.ComplexFrameCoefficientRange
import ComplementedSubspace.ComplexFrameRealification
import ComplementedSubspace.ComplexRecursiveProjection
import ComplementedSubspace.PureFrameDPR

/-! A whole-space real equivalence for the actual pure complex range.

The complex tensor order is one smaller than the real order. Splitting each
complex coefficient into real and imaginary parts produces the extra real
four-row tensor factor. The bounds are uniform over the entire sequence.
-/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

/-- Restrict both directions; Mathlib's equivalence-level restriction in the
pinned version is specialized to endomorphisms. -/
def complexLinearEquivAsReal {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] (e : E ≃L[ℂ] F) : E ≃L[ℝ] F :=
  ContinuousLinearEquiv.equivOfInverse (e.toContinuousLinearMap.restrictScalars ℝ)
    (e.symm.toContinuousLinearMap.restrictScalars ℝ)
    e.symm_apply_apply e.apply_symm_apply

def complexFrameCoefficientFinRangeEquiv (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    ComplexFrameCoefficient n p ≃ₗᵢ[ℂ]
      (complexFinTensorProjection (ENNReal.ofReal p) n).range :=
  (complexFrameCoefficientRangeEquiv n p).trans
    (scalarIsometricConjugateRangeEquiv (complexFramePiLpEquivFin (ENNReal.ofReal p) n) _)

def frameCoefficientCongrOrder {n m : ℕ} (hn : n = m) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] : FrameCoefficient n p ≃ₗᵢ[ℝ] FrameCoefficient m p := by
  subst m
  exact LinearIsometryEquiv.refl ℝ _

namespace RecursiveFrameSelection
variable {η : ℝ} (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)

def predecessorCoefficientBlockRangeEquiv (j : ℕ) :
    ComplexFrameCoefficient ((s.block j).order - 1) (s.block j).exponent ≃ₗᵢ[ℂ]
      (s.predecessorComplexBlockProjection j).range :=
  complexFrameCoefficientFinRangeEquiv _ _

def predecessorBlockRangeRealEquiv (j : ℕ) :
    (s.predecessorComplexBlockProjection j).range ≃L[ℝ]
      FrameCoefficient (s.block j).order (s.block j).exponent :=
  (complexLinearEquivAsReal (s.predecessorCoefficientBlockRangeEquiv j).symm.toContinuousLinearEquiv).trans
    ((complexFrameRealification ((s.block j).order - 1) (s.block j).exponent
      (s.block j).two_lt_exponent.le).trans
      (frameCoefficientCongrOrder (s.predecessor_order_add_one j)
        (s.block j).exponent).toContinuousLinearEquiv)

theorem predecessorBlockRangeRealEquiv_norm_le (j : ℕ) :
    ‖(s.predecessorBlockRangeRealEquiv j).toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖frameCoefficientCongrOrder (s.predecessor_order_add_one j) (s.block j).exponent
    (complexFrameRealification ((s.block j).order - 1) (s.block j).exponent
      (s.block j).two_lt_exponent.le ((s.predecessorCoefficientBlockRangeEquiv j).symm x))‖ ≤ 2 * ‖x‖
  rw [LinearIsometryEquiv.norm_map]
  have h := (complexFrameRealification ((s.block j).order - 1) (s.block j).exponent
    (s.block j).two_lt_exponent.le).toContinuousLinearMap.le_of_opNorm_le
    (complexFrameRealification_norm_le _ _ (s.block j).two_lt_exponent.le)
    ((s.predecessorCoefficientBlockRangeEquiv j).symm x)
  simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.norm_map] using h

theorem predecessorBlockRangeRealEquiv_symm_norm_le (j : ℕ) :
    ‖(s.predecessorBlockRangeRealEquiv j).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  change ‖s.predecessorCoefficientBlockRangeEquiv j
    ((complexFrameRealification ((s.block j).order - 1) (s.block j).exponent
      (s.block j).two_lt_exponent.le).symm
        ((frameCoefficientCongrOrder (s.predecessor_order_add_one j) (s.block j).exponent).symm y))‖ ≤
    1 * ‖y‖
  rw [LinearIsometryEquiv.norm_map]
  have h := (complexFrameRealification ((s.block j).order - 1) (s.block j).exponent
    (s.block j).two_lt_exponent.le).symm.toContinuousLinearMap.le_of_opNorm_le
    (complexFrameRealification_symm_norm_le _ _ (s.block j).two_lt_exponent.le)
    ((frameCoefficientCongrOrder (s.predecessor_order_add_one j) (s.block j).exponent).symm y)
  simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.norm_map] using h

/-- This is an equivalence of the full spaces with their actual norms. -/
def predecessorComplexRangeRealEquiv :
    s.predecessorComplexProjection.range ≃L[ℝ] s.PureFrameCoefficientProfile :=
  (complexLinearEquivAsReal s.predecessorComplexProjectionRangeEquiv.symm.toContinuousLinearEquiv).trans
    (lpUniformEquiv 2 s.predecessorBlockRangeRealEquiv (by norm_num)
      s.predecessorBlockRangeRealEquiv_norm_le zero_le_one
      s.predecessorBlockRangeRealEquiv_symm_norm_le)

end RecursiveFrameSelection
end ComplementedSubspace
