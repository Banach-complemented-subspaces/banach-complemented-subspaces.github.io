import ComplementedSubspace.AmbientUniformConvex
import ComplementedSubspace.LocalHilbertCompactness

/-! Approximate parallelogram estimates pass to dependent `ℓ²` sums and ambient tails. -/

noncomputable section
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

theorem lp_two_approxParallelogram {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {ν : ℝ}
    (hν : ∀ i, ApproxParallelogram (fun x : E i => ‖x‖) ν) :
    ApproxParallelogram (fun x : lp E 2 => ‖x‖) ν := by
  intro x y
  apply hasSum_le _ ((lp_two_hasSum_sq (x + y)).add (lp_two_hasSum_sq (x - y)))
    (((lp_two_hasSum_sq x).add (lp_two_hasSum_sq y)).mul_left (2 * ν))
  intro i
  simpa only [lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply] using hν i (x i) (y i)

theorem finitePiLp_parallelogram_constant_mono {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (2 : ℝ) ^ (2 - 4 / p) ≤ (2 : ℝ) ^ (2 - 4 / q) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hdiv : (4 : ℝ) / q ≤ 4 / p := div_le_div_of_nonneg_left (by norm_num) hp hpq
  linarith

/-- The dependent `ℓ²` sum of blocks from index `N` onward. -/
abbrev AmbientTail (a : BlockParameters) (N : ℕ) := lp (fun j => Block a (N + j)) 2

theorem ambientTail_approxParallelogram (a : BlockParameters) (N : ℕ) :
    ApproxParallelogram (fun x : AmbientTail a N => ‖x‖)
      ((2 : ℝ) ^ (2 - 4 / a.exponent N)) := by
  apply lp_two_approxParallelogram
  intro j
  have hblock : ApproxParallelogram (fun x : Block a (N + j) => ‖x‖)
      ((2 : ℝ) ^ (2 - 4 / a.exponent (N + j))) := block_parallelogram_le a (N + j)
  exact hblock.mono (finitePiLp_parallelogram_constant_mono
    (by linarith [a.two_lt_exponent (N + j)])
    (a.exponent_antitone (Nat.le_add_right N j)))

/-- The actual tail as a linear subspace of the original ambient space. -/
def ambientTailSubmodule (a : BlockParameters) (N : ℕ) : Submodule ℝ (Ambient a) where
  carrier := {x | ∀ j, j < N → x j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j hj
    simp only [lp.coeFn_add, Pi.add_apply, hx j hj, hy j hj, add_zero]
  smul_mem' := by
    intro r x hx j hj
    simp only [lp.coeFn_smul, Pi.smul_apply, hx j hj, smul_zero]

theorem ambientTailSubmodule_approxParallelogram (a : BlockParameters) (N : ℕ) :
    ApproxParallelogram (fun x : ambientTailSubmodule a N => ‖x‖)
      ((2 : ℝ) ^ (2 - 4 / a.exponent N)) := by
  intro x y
  let ν : ℝ := (2 : ℝ) ^ (2 - 4 / a.exponent N)
  change ‖(x : Ambient a) + (y : Ambient a)‖ ^ 2 + ‖(x : Ambient a) - (y : Ambient a)‖ ^ 2 ≤
    2 * ν * (‖(x : Ambient a)‖ ^ 2 + ‖(y : Ambient a)‖ ^ 2)
  apply hasSum_le _ ((lp_two_hasSum_sq ((x : Ambient a) + (y : Ambient a))).add
    (lp_two_hasSum_sq ((x : Ambient a) - (y : Ambient a))))
    (((lp_two_hasSum_sq (x : Ambient a)).add (lp_two_hasSum_sq (y : Ambient a))).mul_left (2 * ν))
  intro j
  simp only [lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply]
  by_cases hj : j < N
  · simp only [x.property j hj, y.property j hj, zero_add, sub_self, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]
  · have hblock : ApproxParallelogram (fun z : Block a j => ‖z‖)
        ((2 : ℝ) ^ (2 - 4 / a.exponent j)) := block_parallelogram_le a j
    exact hblock.mono (finitePiLp_parallelogram_constant_mono
      (by linarith [a.two_lt_exponent j]) (a.exponent_antitone (Nat.le_of_not_gt hj)))
      (x.val j) (y.val j)

end ComplementedSubspace
