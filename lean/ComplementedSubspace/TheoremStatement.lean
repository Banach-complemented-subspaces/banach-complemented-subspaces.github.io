import ComplementedSubspace.AmbientSeparable
import ComplementedSubspace.LocalUnconditional
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Algebra.Order.Module.Defs

/-!
# The precise real main-theorem statement

`RealMainTheoremStatement` is a proposition, not a theorem declaration or an
axiom. Its proof is `realMainTheorem` in `RealMainTheorem.lean`.
Its parameters and four range/dual conclusions are those of the main
theorem in `1-Introduction.tex` of the supplied manuscript.

The target asks for uniform convexity in the inherited ambient norm, a stronger
property proved in the manuscript's construction. The analytic implication to
superreflexivity has not been formalized here, and no such implication is
assumed. In particular, this file does not confuse Banach-space reflexivity
with the algebraic notion of module reflexivity.

The lattice-order predicate below has its actual mathematical definition. It
preserves the existing normed real vector space and its complete metric; only
the compatible lattice order is existentially quantified.
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace ComplementedSubspace

/-- A compatible real Banach lattice order on an existing real Banach space.
The norm and scalar multiplication remain the inherited ones. -/
def HasRealBanachLatticeOrder (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] : Prop :=
  ∃ latticeOrder : Lattice X,
    letI : Lattice X := latticeOrder
    IsOrderedAddMonoid X ∧ PosSMulMono ℝ X ∧ HasSolidNorm X

/-- The two quantitative local-structure assertions for a projection range
and its continuous dual, with their inherited and operator norms. -/
def HasSeparatedRange {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : X →L[ℝ] X) : Prop :=
  chiGL ↥P.range ≤ ‖P‖ₑ ∧
  chiDPR ↥P.range = ⊤ ∧
  chiGL (↥P.range →L[ℝ] ℝ) ≤ ‖P‖ₑ ∧
  chiDPR (↥P.range →L[ℝ] ℝ) = ⊤

/-- The real main-theorem target, with the stronger uniform-convexity property
of the constructed ambient space. Proved in `RealMainTheorem.lean`.

`BlockParameters` records positive dimensions, exponents in `(2,3]`, monotone
decrease, and convergence to two. `Ambient` is the actual dependent counting-
norm `ℓ²` sum of those finite `ℓᵖ` blocks. -/
def RealMainTheoremStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    ∃ a : BlockParameters,
      TopologicalSpace.SeparableSpace (Ambient a) ∧
      UniformConvexSpace (Ambient a) ∧
      HasRealBanachLatticeOrder (Ambient a) ∧
      ∃ P : Ambient a →L[ℝ] Ambient a,
        P.comp P = P ∧
        ‖P‖ < 1 + ρ ∧
        ‖ContinuousLinearMap.id ℝ (Ambient a) - P‖ < 1 + ρ ∧
        HasSeparatedRange P ∧
        HasSeparatedRange (ContinuousLinearMap.id ℝ (Ambient a) - P)

end ComplementedSubspace
