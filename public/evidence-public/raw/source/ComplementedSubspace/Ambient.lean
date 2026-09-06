import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Data.PNat.Defs
import Mathlib.Tactic.NormNum

/-!
# The ambient countable sum

The finite blocks use the counting-measure `ℓᵖ` norm. The outer space is the
dependent `ℓ²` sum of these blocks. This file constructs the actual normed and
complete spaces and their coordinate projections; it does not claim the
Banach lattice or uniform convexity instances have been proved.
-/

noncomputable section

open scoped ENNReal Topology

namespace ComplementedSubspace

/-- The parameters required by the real main theorem. -/
structure BlockParameters where
  dimension : ℕ → ℕ+
  exponent : ℕ → ℝ
  two_lt_exponent : ∀ j, 2 < exponent j
  exponent_le_three : ∀ j, exponent j ≤ 3
  exponent_antitone : Antitone exponent
  exponent_tendsto : Filter.Tendsto exponent Filter.atTop (𝓝 2)

instance (a : BlockParameters) (j : ℕ) :
    Fact (1 ≤ ENNReal.ofReal (a.exponent j)) := by
  constructor
  have h : (1 : ℝ) ≤ a.exponent j :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (a.two_lt_exponent j).le
  simpa using ENNReal.ofReal_le_ofReal h

/-- A finite real block with its genuine `ℓᵖ` norm. -/
abbrev Block (a : BlockParameters) (j : ℕ) :=
  PiLp (ENNReal.ofReal (a.exponent j)) (fun _ : Fin (a.dimension j) => ℝ)

/-- The actual ambient space `(⨁ j, ℓ^(p j)^(N j))₂`. -/
abbrev Ambient (a : BlockParameters) := lp (Block a) 2

example (a : BlockParameters) (j : ℕ) : CompleteSpace (Block a j) := inferInstance
example (a : BlockParameters) : NormedSpace ℝ (Ambient a) := inferInstance
example (a : BlockParameters) : CompleteSpace (Ambient a) := inferInstance

/-- Isometric inclusion of one block into the ambient space. -/
def blockInclusion (a : BlockParameters) (j : ℕ) : Block a j →L[ℝ] Ambient a :=
  lp.singleContinuousLinearMap ℝ (Block a) 2 j

/-- Evaluation at one block. -/
def blockEvaluation (a : BlockParameters) (j : ℕ) : Ambient a →L[ℝ] Block a j :=
  lp.evalCLM ℝ (Block a) 2 j

/-- Projection onto the chosen block, as an endomorphism of the ambient space. -/
def blockProjection (a : BlockParameters) (j : ℕ) : Ambient a →L[ℝ] Ambient a :=
  (blockInclusion a j).comp (blockEvaluation a j)

@[simp]
theorem blockEvaluation_blockInclusion (a : BlockParameters) (j : ℕ) (x : Block a j) :
    blockEvaluation a j (blockInclusion a j x) = x := by
  change (lp.single 2 j x) j = x
  simp

@[simp]
theorem norm_blockInclusion (a : BlockParameters) (j : ℕ) (x : Block a j) :
    ‖blockInclusion a j x‖ = ‖x‖ := by
  exact lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2) j x

theorem blockProjection_idempotent (a : BlockParameters) (j : ℕ) :
    (blockProjection a j).comp (blockProjection a j) = blockProjection a j := by
  ext x
  simp [blockProjection]

theorem norm_blockProjection_apply_le (a : BlockParameters) (j : ℕ) (x : Ambient a) :
    ‖blockProjection a j x‖ ≤ ‖x‖ := by
  change ‖blockInclusion a j (blockEvaluation a j x)‖ ≤ ‖x‖
  rw [norm_blockInclusion]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x j

theorem norm_blockProjection_le_one (a : BlockParameters) (j : ℕ) :
    ‖blockProjection a j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_blockProjection_apply_le a j x

/-- Every vector is the unconditionally convergent sum of its block components. -/
theorem hasSum_blockProjection (a : BlockParameters) (x : Ambient a) :
    HasSum (fun j => blockProjection a j x) x := by
  exact lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x

end ComplementedSubspace
