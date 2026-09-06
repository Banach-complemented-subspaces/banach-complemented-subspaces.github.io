import ComplementedSubspace.LocalHilbert

noncomputable section

namespace ComplementedSubspace

/-- A dimension-bounded Hilbert approximation property, with finite dimension
explicitly required so that infinite dimensional subspaces are not mistaken
for dimension zero by `finrank`. -/
def LocallyHilbertWithin (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (D : ℝ) : Prop :=
  ∀ (S : Submodule ℝ E) [FiniteDimensional ℝ S],
    Module.finrank ℝ S ≤ d → HasHilbertNormWithin S D

/-- Local Hilbert control after taking the dual of an arbitrary subspace. -/
def DualSubspacesLocallyHilbertWithin (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (D : ℝ) : Prop :=
  ∀ V : Submodule ℝ E, LocallyHilbertWithin (StrongDual ℝ V) d D

/-- The same property on dual subspaces of E. Naming the source first keeps
its inherited normed instances fixed when E is an iterated projection kernel. -/
def DualSubspaceDualHilbertWithin (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (D : ℝ) : Prop :=
  DualSubspacesLocallyHilbertWithin (StrongDual ℝ E) d D

end ComplementedSubspace
