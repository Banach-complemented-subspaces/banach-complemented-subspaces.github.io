import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex

/-! A dimension-independent bound for finite real multipliers, obtained from
the convex hull of the vertices of a cube. -/

noncomputable section
open scoped BigOperators

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_linearMap_le_of_cube_vertices {ι : Type*} [Fintype ι]
    (L : (ι → ℝ) →ₗ[ℝ] E) (R : ℝ)
    (hL : ∀ ε : ι → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) → ‖L ε‖ ≤ R)
    (θ : ι → ℝ) (hθ : ∀ i, ‖θ i‖ ≤ 1) : ‖L θ‖ ≤ R := by
  have hmem : θ ∈ convexHull ℝ ((Set.univ : Set ι).pi (fun _ => ({-1, 1} : Set ℝ))) := by
    apply mem_convexHull_pi
    intro i _
    rw [convexHull_pair, segment_eq_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hθ i)
  have hsub : (Set.univ : Set ι).pi (fun _ => ({-1, 1} : Set ℝ)) ⊆
      L ⁻¹' Metric.closedBall 0 R := by
    intro ε hε
    apply mem_closedBall_zero_iff.mpr
    apply hL ε
    intro i
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hε i (Set.mem_univ i)
  exact mem_closedBall_zero_iff.mp
    (convexHull_min hsub ((convex_closedBall (0 : E) R).linear_preimage L) hmem)

/-- A uniform bound on all partial subsums controls every real multiplier in
the unit interval in absolute value, with the dimension-independent factor 2. -/
theorem norm_sum_smul_le_of_subsum_bound {ι : Type*} [Fintype ι]
    (v : ι → E) (K : ℝ) (hK : ∀ s : Finset ι, ‖∑ i ∈ s, v i‖ ≤ K)
    (θ : ι → ℝ) (hθ : ∀ i, ‖θ i‖ ≤ 1) : ‖∑ i, θ i • v i‖ ≤ 2 * K := by
  classical
  apply norm_linearMap_le_of_cube_vertices (Fintype.linearCombination ℝ v) (2 * K) _ θ hθ
  intro ε hε
  have heq : (∑ i, ε i • v i) =
      (∑ i ∈ Finset.univ.filter (fun i => ε i = 1), v i) -
      (∑ i ∈ Finset.univ.filter (fun i => ε i = -1), v i) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases hε i with hi | hi <;> norm_num [hi]
  change ‖∑ i, ε i • v i‖ ≤ 2 * K
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add (hK _) (hK _)).trans_eq (by ring))

end ComplementedSubspace

