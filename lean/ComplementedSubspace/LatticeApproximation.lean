import ComplementedSubspace.LatticeBasis
import ComplementedSubspace.FiniteApproximation
import BanLat.Dual

/-!+# Finite unconditional approximation in order-complete lattices

This is the interface between the spectral construction and the exact finite
superspace perturbation argument. It applies in particular to dual lattices.
-/

noncomputable section

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E]

theorem hasFiniteUnconditionalApproximations_of_principalProjectionProperty
    [HasPrincipalProjectionProperty E] :
    HasFiniteUnconditionalApproximations E 1 := by
  intro m x δ hδ
  obtain ⟨P, u, _, _, hP⟩ := exists_finite_disjoint_approximation x hδ
  obtain ⟨n, b, hb⟩ := P.exists_unconditional_basis u
  refine ⟨P.cellSpan u, n, b, by simpa using hb, ?_⟩
  intro i
  obtain ⟨y, hy, hey⟩ := hP i
  refine ⟨⟨y, hy⟩, ?_⟩
  simpa only [norm_sub_rev] using hey.le

theorem hasFiniteUnconditionalApproximations_of_orderComplete
    {F : Type*} [NormedAddCommGroup F] [ConditionallyCompleteLattice F]
    [IsOrderedAddMonoid F] [NormedVectorLattice F] :
    HasFiniteUnconditionalApproximations F 1 :=
  hasFiniteUnconditionalApproximations_of_principalProjectionProperty

theorem hasFiniteUnconditionalApproximations_dual
    {F : Type*} [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
    [BanachLattice F] : HasFiniteUnconditionalApproximations (StrongDual ℝ F) 1 :=
  hasFiniteUnconditionalApproximations_of_orderComplete

theorem chiDPR_dual_lattice_le_one
    {F : Type*} [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
    [BanachLattice F] : chiDPR (StrongDual ℝ F) ≤ 1 :=
  chiDPR_le_constant_of_finite_approximations 1 le_rfl
    hasFiniteUnconditionalApproximations_dual

/-- The only general lattice DPR theorem required by the nonlattice shortcut:
the dual of every real Banach lattice has finite DPR constant. -/
theorem hasDPRLocalUnconditionalStructure_dual_lattice
    {F : Type*} [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
    [BanachLattice F] : HasDPRLocalUnconditionalStructure (StrongDual ℝ F) :=
  chiDPR_dual_lattice_le_one.trans_lt (by simp)

end ComplementedSubspace
