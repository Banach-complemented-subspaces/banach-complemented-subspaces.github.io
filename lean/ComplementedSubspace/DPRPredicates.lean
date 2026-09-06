import ComplementedSubspace.LocalUnconditional

/-! Cached source instances for DPR assertions on iterated continuous duals. -/

noncomputable section
namespace ComplementedSubspace

def HasInfiniteDualDPR (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  chiDPR (StrongDual ℝ E) = ⊤

def HasInfiniteBidualDPR (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  HasInfiniteDualDPR (StrongDual ℝ E)

end ComplementedSubspace
