import ComplementedSubspace.Ambient
import ComplementedSubspace.LpTwoUniformConvex
import Mathlib.Topology.Algebra.Module.Basic

/-! The actual complex dependent sum, with its inherited norm and complex
scalar multiplication. Finite-Lp and outer-L2 geometry are reused unchanged. -/
noncomputable section
open scoped ENNReal Topology
open TopologicalSpace
namespace ComplementedSubspace
/-- A finite complex block with its genuine `ℓᵖ` norm. -/
abbrev ComplexBlock (a : BlockParameters) (j : ℕ) :=
  PiLp (ENNReal.ofReal (a.exponent j)) (fun _ : Fin (a.dimension j) => ℂ)

/-- The actual complex ambient space `(⨁ j, ℓ^(p j)^(N j))₂`. -/
abbrev ComplexAmbient (a : BlockParameters) := lp (ComplexBlock a) 2

example (a : BlockParameters) (j : ℕ) : CompleteSpace (ComplexBlock a j) := inferInstance
example (a : BlockParameters) : NormedSpace ℂ (ComplexAmbient a) := inferInstance
example (a : BlockParameters) : CompleteSpace (ComplexAmbient a) := inferInstance

/-- Isometric inclusion of one complexBlock into the complexAmbient space. -/
def complexBlockInclusion (a : BlockParameters) (j : ℕ) : ComplexBlock a j →L[ℂ] ComplexAmbient a :=
  lp.singleContinuousLinearMap ℂ (ComplexBlock a) 2 j

/-- Evaluation at one complexBlock. -/
def complexBlockEvaluation (a : BlockParameters) (j : ℕ) : ComplexAmbient a →L[ℂ] ComplexBlock a j :=
  lp.evalCLM ℂ (ComplexBlock a) 2 j

/-- Projection onto the chosen complexBlock, as an endomorphism of the complexAmbient space. -/
def complexBlockProjection (a : BlockParameters) (j : ℕ) : ComplexAmbient a →L[ℂ] ComplexAmbient a :=
  (complexBlockInclusion a j).comp (complexBlockEvaluation a j)

@[simp]
theorem complexBlockEvaluation_complexBlockInclusion (a : BlockParameters) (j : ℕ) (x : ComplexBlock a j) :
    complexBlockEvaluation a j (complexBlockInclusion a j x) = x := by
  change (lp.single 2 j x) j = x
  simp

@[simp]
theorem norm_complexBlockInclusion (a : BlockParameters) (j : ℕ) (x : ComplexBlock a j) :
    ‖complexBlockInclusion a j x‖ = ‖x‖ := by
  exact lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2) j x

theorem complexBlockProjection_idempotent (a : BlockParameters) (j : ℕ) :
    (complexBlockProjection a j).comp (complexBlockProjection a j) = complexBlockProjection a j := by
  ext x
  simp [complexBlockProjection]

theorem norm_complexBlockProjection_apply_le (a : BlockParameters) (j : ℕ) (x : ComplexAmbient a) :
    ‖complexBlockProjection a j x‖ ≤ ‖x‖ := by
  change ‖complexBlockInclusion a j (complexBlockEvaluation a j x)‖ ≤ ‖x‖
  rw [norm_complexBlockInclusion]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x j

theorem norm_complexBlockProjection_le_one (a : BlockParameters) (j : ℕ) :
    ‖complexBlockProjection a j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_complexBlockProjection_apply_le a j x

/-- Every vector is the unconditionally convergent sum of its complexBlock components. -/
theorem hasSum_complexBlockProjection (a : BlockParameters) (x : ComplexAmbient a) :
    HasSum (fun j => complexBlockProjection a j x) x := by
  exact lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x


instance complexAmbientSeparableSpace (a : BlockParameters) : SeparableSpace (ComplexAmbient a) := by
  let s : Set (ComplexAmbient a) := ⋃ j, Set.range (complexBlockInclusion a j)
  let W : Submodule ℂ (ComplexAmbient a) := Submodule.span ℂ s
  have hs : IsSeparable s :=
    .iUnion fun j => isSeparable_range (complexBlockInclusion a j).continuous
  have hW : IsSeparable (W : Set (ComplexAmbient a)) := hs.span
  have hdense : Dense (W : Set (ComplexAmbient a)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    apply top_unique
    intro x _
    apply W.isClosed_topologicalClosure.mem_of_tendsto (hasSum_complexBlockProjection a x)
    apply Filter.Eventually.of_forall
    intro t
    apply W.topologicalClosure.sum_mem
    intro j _
    apply W.le_topologicalClosure
    apply Submodule.subset_span
    exact Set.mem_iUnion.mpr ⟨j, complexBlockEvaluation a j x, rfl⟩
  exact hdense.isSeparable_iff.mp hW


theorem complexBlock_hasCubicSumModulus (a : BlockParameters) (j : ℕ) :
    HasCubicSumModulus (ComplexBlock a j) := by
  intro ε hε x y hx hy hxy
  exact finitePiLp_uniform_modulus (a.two_lt_exponent j).le (a.exponent_le_three j)
    x y hx hy hε hxy

instance complexAmbientUniformConvexSpace (a : BlockParameters) : UniformConvexSpace (ComplexAmbient a) :=
  lp_two_uniformConvexSpace_of_cubicModulus (complexBlock_hasCubicSumModulus a)

theorem complexBlock_parallelogram_le (a : BlockParameters) (j : ℕ) (x y : ComplexBlock a j) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 ≤
      2 * (2 : ℝ) ^ (2 - 4 / a.exponent j) * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  finitePiLp_parallelogram_le (a.two_lt_exponent j).le x y

theorem complexBlock_parallelogram_constant_ge_one (a : BlockParameters) (j : ℕ) :
    1 ≤ (2 : ℝ) ^ (2 - 4 / a.exponent j) :=
  finitePiLp_parallelogram_constant_ge_one (a.two_lt_exponent j).le

theorem complexBlock_parallelogram_constant_tendsto (a : BlockParameters) :
    Filter.Tendsto (fun j => (2 : ℝ) ^ (2 - 4 / a.exponent j)) Filter.atTop (𝓝 1) :=
  finitePiLp_parallelogram_constant_tendsto.comp a.exponent_tendsto

end ComplementedSubspace

