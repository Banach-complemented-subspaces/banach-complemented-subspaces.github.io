import ComplementedSubspace.RecursiveHeadHilbert
import ComplementedSubspace.LpTwoParallelogram
import ComplementedSubspace.LocalHilbertProperty

/-! The recursive exponent restrictions give the required local Hilbert
estimate on every inherited profile tail after the selected coordinate. -/
noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

theorem blockSubspace_approxParallelogram (a : BlockParameters) (i : ℕ)
    (V : Submodule ℝ (Block a i)) :
    ApproxParallelogram (fun x : V => ‖x‖) ((2 : ℝ) ^ (2 - 4 / a.exponent i)) := by
  intro x y
  change ‖((x : Block a i) + (y : Block a i))‖ ^ 2 +
    ‖((x : Block a i) - (y : Block a i))‖ ^ 2 ≤
      2 * ((2 : ℝ) ^ (2 - 4 / a.exponent i)) * (‖(x : Block a i)‖ ^ 2 + ‖(y : Block a i)‖ ^ 2)
  exact block_parallelogram_le a i (x : Block a i) (y : Block a i)

variable {η : ℝ} (s : RecursiveFrameSelection η recursiveFrameExponentTolerance)
  (S : ∀ i : ℕ, Submodule ℝ (Block s.toBlockParameters i))

abbrev RecursiveProfileTail (j : ℕ) := lp (fun k => S (j + 1 + k)) 2

theorem recursiveProfileTail_approxParallelogram (j : ℕ) :
    ApproxParallelogram (fun x : RecursiveProfileTail s S j => ‖x‖)
      (recursiveLocalHilbertThreshold (3 * 2 ^ (s.block j).order)) := by
  apply lp_two_approxParallelogram
  intro k
  have hsmall := s.later_exponent_small j (j + 1 + k) (by omega)
  have hν := recursiveFrameExponentTolerance_spec (s.block j).order
    (s.block (j + 1 + k)).two_lt_exponent.le hsmall
  have hb : ApproxParallelogram (fun x : S (j + 1 + k) => ‖x‖)
      ((2 : ℝ) ^ (2 - 4 / (s.block (j + 1 + k)).exponent)) := by
    exact blockSubspace_approxParallelogram s.toBlockParameters (j + 1 + k) (S (j + 1 + k))
  exact hb.mono hν.le

theorem recursiveProfileTail_locallyHilbert (j : ℕ) :
    LocallyHilbertWithin (RecursiveProfileTail s S j) (3 * 2 ^ (s.block j).order) 2 := by
  intro V _ hV
  exact recursiveLocalHilbertThreshold_spec (3 * 2 ^ (s.block j).order)
    (RecursiveProfileTail s S j) (recursiveProfileTail_approxParallelogram s S j) V hV

end ComplementedSubspace
