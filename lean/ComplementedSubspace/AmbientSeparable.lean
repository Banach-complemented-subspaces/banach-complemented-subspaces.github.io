import ComplementedSubspace.Ambient
import Mathlib.Topology.Algebra.Module.Basic

/-! # Separability of the actual ambient space

The span of the union of the countably many finite block images is separable.
The unconditional block expansion shows this span is dense.
-/

noncomputable section

open TopologicalSpace

namespace ComplementedSubspace

instance ambientSeparableSpace (a : BlockParameters) : SeparableSpace (Ambient a) := by
  let s : Set (Ambient a) := ⋃ j, Set.range (blockInclusion a j)
  let W : Submodule ℝ (Ambient a) := Submodule.span ℝ s
  have hs : IsSeparable s :=
    .iUnion fun j => isSeparable_range (blockInclusion a j).continuous
  have hW : IsSeparable (W : Set (Ambient a)) := hs.span
  have hdense : Dense (W : Set (Ambient a)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    apply top_unique
    intro x _
    apply W.isClosed_topologicalClosure.mem_of_tendsto (hasSum_blockProjection a x)
    apply Filter.Eventually.of_forall
    intro t
    apply W.topologicalClosure.sum_mem
    intro j _
    apply W.le_topologicalClosure
    apply Submodule.subset_span
    exact Set.mem_iUnion.mpr ⟨j, blockEvaluation a j x, rfl⟩
  exact hdense.isSeparable_iff.mp hW

end ComplementedSubspace
