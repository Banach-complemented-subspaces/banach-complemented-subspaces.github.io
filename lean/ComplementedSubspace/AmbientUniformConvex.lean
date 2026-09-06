import ComplementedSubspace.Ambient
import ComplementedSubspace.LpTwoUniformConvex

/-! Uniform convexity and asymptotic parallelogram constants for the actual ambient space. -/

noncomputable section
open scoped ENNReal Topology

namespace ComplementedSubspace

theorem block_hasCubicSumModulus (a : BlockParameters) (j : ℕ) :
    HasCubicSumModulus (Block a j) := by
  intro ε hε x y hx hy hxy
  exact finitePiLp_uniform_modulus (a.two_lt_exponent j).le (a.exponent_le_three j)
    x y hx hy hε hxy

instance ambientUniformConvexSpace (a : BlockParameters) : UniformConvexSpace (Ambient a) :=
  lp_two_uniformConvexSpace_of_cubicModulus (block_hasCubicSumModulus a)

theorem block_parallelogram_le (a : BlockParameters) (j : ℕ) (x y : Block a j) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 ≤
      2 * (2 : ℝ) ^ (2 - 4 / a.exponent j) * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  finitePiLp_parallelogram_le (a.two_lt_exponent j).le x y

theorem block_parallelogram_constant_ge_one (a : BlockParameters) (j : ℕ) :
    1 ≤ (2 : ℝ) ^ (2 - 4 / a.exponent j) :=
  finitePiLp_parallelogram_constant_ge_one (a.two_lt_exponent j).le

theorem block_parallelogram_constant_tendsto (a : BlockParameters) :
    Filter.Tendsto (fun j => (2 : ℝ) ^ (2 - 4 / a.exponent j)) Filter.atTop (𝓝 1) :=
  finitePiLp_parallelogram_constant_tendsto.comp a.exponent_tendsto

end ComplementedSubspace
