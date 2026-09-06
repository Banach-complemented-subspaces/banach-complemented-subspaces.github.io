import ComplementedSubspace.ComplexAmbient
import ComplementedSubspace.ComplexReindexedFrameProjection
import ComplementedSubspace.LpSubmoduleScalar

/-! The pure complex frame projection uses one fewer tensor factor than the
real recursive frame. Its range realifies to the distinguished real profile. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace
namespace RecursiveFrameSelection

variable {η : ℝ} {θ : ℕ → ℝ} (s : RecursiveFrameSelection η θ)

def predecessorBlockParameters : BlockParameters where
  dimension j := ⟨4 ^ ((s.block j).order - 1), by positivity⟩
  exponent j := (s.block j).exponent
  two_lt_exponent j := (s.block j).two_lt_exponent
  exponent_le_three j := (s.block j).exponent_le_three
  exponent_antitone := s.exponent_strictAnti.antitone
  exponent_tendsto := s.exponent_tendsto

@[simp] theorem predecessorBlockParameters_dimension (j : ℕ) :
    (s.predecessorBlockParameters.dimension j : ℕ) = 4 ^ ((s.block j).order - 1) := rfl

@[simp] theorem predecessorBlockParameters_exponent (j : ℕ) :
    s.predecessorBlockParameters.exponent j = (s.block j).exponent := rfl

theorem predecessor_order_add_one (j : ℕ) : (s.block j).order - 1 + 1 = (s.block j).order := by
  have h := (s.block j).order_pos
  omega

def predecessorComplexBlockProjection (j : ℕ) :
    ComplexBlock s.predecessorBlockParameters j →L[ℂ]
      ComplexBlock s.predecessorBlockParameters j :=
  complexFinTensorProjection (ENNReal.ofReal (s.block j).exponent) ((s.block j).order - 1)

theorem predecessorComplexBlockProjection_idempotent (j : ℕ) :
    (s.predecessorComplexBlockProjection j).comp (s.predecessorComplexBlockProjection j) =
      s.predecessorComplexBlockProjection j :=
  complexFinTensorProjection_idempotent _ _

theorem one_le_predecessorComplexBlockProjection_norm (j : ℕ) :
    1 ≤ ‖s.predecessorComplexBlockProjection j‖ :=
  one_le_complexFinTensorProjection_norm _ _

theorem predecessorComplexBlockProjection_norm_le (j : ℕ) :
    ‖s.predecessorComplexBlockProjection j‖ ≤ Real.exp (18 * η) := by
  apply (complexFinTensorProjection_norm_le_exp (s.block j).two_lt_exponent.le
    (s.block j).exponent_le_three ((s.block j).order - 1)).trans
  apply Real.exp_le_exp.mpr
  have hm : (((s.block j).order - 1 : ℕ) : ℝ) ≤ ((s.block j).order : ℝ) := by
    exact_mod_cast Nat.sub_le (s.block j).order 1
  have hmul := mul_le_mul_of_nonneg_right hm (sq_nonneg ((s.block j).exponent - 2))
  have h := s.quadratic_error j
  dsimp [FiniteFrameChoice.epsilon] at h
  nlinarith only [h, hmul]

def predecessorComplexProjection :
    ComplexAmbient s.predecessorBlockParameters →L[ℂ]
      ComplexAmbient s.predecessorBlockParameters :=
  lpDiagonal 2 s.predecessorComplexBlockProjection (Real.exp_pos _).le
    s.predecessorComplexBlockProjection_norm_le

@[simp] theorem predecessorComplexProjection_apply
    (x : ComplexAmbient s.predecessorBlockParameters) (j : ℕ) :
    s.predecessorComplexProjection x j = s.predecessorComplexBlockProjection j (x j) := rfl

theorem predecessorComplexProjection_idempotent :
    s.predecessorComplexProjection.comp s.predecessorComplexProjection =
      s.predecessorComplexProjection :=
  lpDiagonal_idempotent 2 _ _ _ s.predecessorComplexBlockProjection_idempotent

theorem predecessorComplexProjection_norm_le :
    ‖s.predecessorComplexProjection‖ ≤ Real.exp (18 * η) :=
  lpDiagonal_norm_le 2 _ _ _

theorem one_le_predecessorComplexProjection_norm : 1 ≤ ‖s.predecessorComplexProjection‖ := by
  exact (s.one_le_predecessorComplexBlockProjection_norm 0).trans
    (lpDiagonal_component_norm_le 2 s.predecessorComplexBlockProjection (Real.exp_pos _).le
      s.predecessorComplexBlockProjection_norm_le 0)

def predecessorComplexProjectionRangeEquiv :
    lp (fun j => (s.predecessorComplexBlockProjection j).range) 2 ≃ₗᵢ[ℂ]
      s.predecessorComplexProjection.range :=
  lpDiagonalRangeEquivScalar s.predecessorComplexBlockProjection (Real.exp_pos _).le
    s.predecessorComplexBlockProjection_norm_le s.predecessorComplexBlockProjection_idempotent

@[simp] theorem predecessorComplexProjectionRangeEquiv_apply
    (x : lp (fun j => (s.predecessorComplexBlockProjection j).range) 2) (j : ℕ) :
    (s.predecessorComplexProjectionRangeEquiv x : ComplexAmbient s.predecessorBlockParameters) j =
      (x j : ComplexBlock s.predecessorBlockParameters j) := rfl

end RecursiveFrameSelection

/-- The actual pure complex diagonal projection has norm arbitrarily close
to one from above, with its block and range formulas retained. -/
theorem exists_recursive_predecessorComplexProjection_near_one {B : ℝ} (hB : 1 < B) :
    ∃ (η : ℝ) (hη : 0 < η),
      ‖(recursiveFrameSelection hη).predecessorComplexProjection‖ < B := by
  let η := Real.log B / 36
  have hlog : 0 < Real.log B := Real.log_pos hB
  have hη : 0 < η := div_pos hlog (by norm_num)
  refine ⟨η, hη, ?_⟩
  calc
    _ ≤ Real.exp (18 * η) :=
      (recursiveFrameSelection hη).predecessorComplexProjection_norm_le
    _ < Real.exp (Real.log B) := by
      apply Real.exp_lt_exp.mpr
      dsimp [η]
      linarith
    _ = B := Real.exp_log ((by norm_num : (0 : ℝ) < 1).trans hB)

end ComplementedSubspace
