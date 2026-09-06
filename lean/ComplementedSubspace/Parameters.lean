import ComplementedSubspace.Ambient
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

/-!
# Explicit admissible block parameters

For any positive integer dimensions, the sequence `p j = 2 + 1 / (j + 1)`
provides admissible exponents. This constructs actual `BlockParameters`;
it makes no assertion that arbitrary dimensions satisfy the additional
requirements of the main theorem's separation construction.
-/

noncomputable section

open scoped Topology

namespace ComplementedSubspace

/-- An explicit sequence of finite exponents decreasing to two. -/
def canonicalExponent (j : ℕ) : ℝ := 2 + 1 / ((j : ℝ) + 1)

theorem two_lt_canonicalExponent (j : ℕ) : 2 < canonicalExponent j := by
  exact lt_add_of_pos_right 2 (by positivity)

theorem canonicalExponent_le_three (j : ℕ) : canonicalExponent j ≤ 3 := by
  have h : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (le_add_of_nonneg_left (Nat.cast_nonneg j))
  calc
    canonicalExponent j ≤ 2 + 1 := add_le_add (le_refl 2) h
    _ = 3 := by norm_num

theorem canonicalExponent_antitone : Antitone canonicalExponent := by
  intro i j hij
  have hij' : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
  change 2 + 1 / ((j : ℝ) + 1) ≤ 2 + 1 / ((i : ℝ) + 1)
  exact add_le_add (le_refl 2) (one_div_le_one_div_of_le (by positivity)
    (add_le_add hij' (le_refl 1)))

theorem canonicalExponent_tendsto :
    Filter.Tendsto canonicalExponent Filter.atTop (𝓝 2) := by
  change Filter.Tendsto (fun j : ℕ => 2 + 1 / ((j : ℝ) + 1)) Filter.atTop (𝓝 2)
  simpa only [add_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Admissible exponents for any specified sequence of positive dimensions. -/
def canonicalBlockParameters (N : ℕ → ℕ+) : BlockParameters where
  dimension := N
  exponent := canonicalExponent
  two_lt_exponent := two_lt_canonicalExponent
  exponent_le_three := canonicalExponent_le_three
  exponent_antitone := canonicalExponent_antitone
  exponent_tendsto := canonicalExponent_tendsto

@[simp]
theorem canonicalBlockParameters_dimension (N : ℕ → ℕ+) :
    (canonicalBlockParameters N).dimension = N := rfl

@[simp]
theorem canonicalBlockParameters_exponent (N : ℕ → ℕ+) (j : ℕ) :
    (canonicalBlockParameters N).exponent j = 2 + 1 / ((j : ℝ) + 1) := rfl

/-- The ambient-space parameter type is inhabited. -/
theorem blockParameters_nonempty : Nonempty BlockParameters :=
  ⟨canonicalBlockParameters (fun _ => 1)⟩

end ComplementedSubspace
