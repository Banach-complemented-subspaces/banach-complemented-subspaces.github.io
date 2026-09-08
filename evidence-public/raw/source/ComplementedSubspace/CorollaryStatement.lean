import ComplementedSubspace.TheoremStatement
import Mathlib.Analysis.Normed.Module.Bases
import Mathlib.Analysis.Complex.Basic

/-!
# Exact corollary statements

This file defines the propositions proved by `realCorollary`,
`realUnconditionalCorollary`, and `realSeparableNonprimarity` in
`RealMainConsequences.lean`, and by `complexCorollary` in
`ComplexCorollary.lean`. The scalar multiplier condition uses all scalars of
norm at most one, including complex phases over the complex field.

Superreflexivity is expressed by its standard equivalent-uniformly-convex-norm
characterization: bounded linear isomorphism to a complete uniformly convex
space. We do not substitute algebraic module reflexivity for this property.
-/

noncomputable section
universe u

namespace ComplementedSubspace

/-- A Banach-space witness, carrying its actual norm and scalar structure. -/
structure BanachModel (𝕜 : Type*) [NontriviallyNormedField 𝕜] where
  Carrier : Type u
  normedGroup : NormedAddCommGroup Carrier
  normedSpace : letI := normedGroup; NormedSpace 𝕜 Carrier
  completeSpace : letI := normedGroup; CompleteSpace Carrier

attribute [instance] BanachModel.normedGroup BanachModel.normedSpace BanachModel.completeSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Existence of a finite or sequential unconditional Schauder basis, matching
the manuscript's finite-or-natural-number index convention. The finite case
includes the empty basis of the zero space. Both cases use Mathlib's actual
biorthogonal continuous coordinates and unconditional convergence. -/
def HasUnconditionalSchauderBasis (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  (∃ n : ℕ, Nonempty (UnconditionalSchauderBasis (Fin n) 𝕜 E)) ∨
    Nonempty (UnconditionalSchauderBasis ℕ 𝕜 E)

/-- Contractivity for every finitely supported scalar multiplier, not just
coordinate projections. -/
def IsOneUnconditional (b : UnconditionalSchauderBasis ℕ 𝕜 E) : Prop :=
  ∀ (s : Finset ℕ) (θ : ℕ → 𝕜), (∀ i, ‖θ i‖ ≤ 1) →
    ∀ x : E, ‖∑ i ∈ s, (θ i * b.coord i x) • b i‖ ≤ ‖x‖

/-- An actual infinite sequence forming a 1-unconditional Schauder basis.
This stronger ambient witness is sufficient for the corollaries. Their
negative range conclusions use `HasUnconditionalSchauderBasis`, which also
counts finite bases and therefore excludes finite-dimensional loopholes. -/
def HasOneUnconditionalSchauderBasis (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∃ b : UnconditionalSchauderBasis ℕ 𝕜 E, IsOneUnconditional b

/-- The uniformly convex renormability characterization of superreflexivity. -/
def IsSuperreflexiveByRenorming (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∃ H : BanachModel.{u} 𝕜,
    UniformConvexSpace H.Carrier ∧ Nonempty (E ≃L[𝕜] H.Carrier)

/-- The quantified target is any real Banach lattice with any equivalent
norm, not just a lattice order compatible with E's current norm. -/
def IsIsomorphicToRealBanachLattice (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Prop :=
  ∃ L : BanachModel.{u} ℝ,
    HasRealBanachLatticeOrder L.Carrier ∧ Nonempty (E ≃L[ℝ] L.Carrier)

/-- The unconditional-basis corollary at one scalar field. -/
def UnconditionalCorollaryStatement (𝕜 : Type*) [NontriviallyNormedField 𝕜] : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ X : BanachModel.{0} 𝕜,
    HasOneUnconditionalSchauderBasis 𝕜 X.Carrier ∧
    ∃ P : X.Carrier →L[𝕜] X.Carrier,
      P.comp P = P ∧ ‖P‖ < 1 + ρ ∧
      ¬ HasUnconditionalSchauderBasis 𝕜 P.range ∧
      ¬ HasUnconditionalSchauderBasis 𝕜 (P.range →L[𝕜] 𝕜)

/-- The real corollary includes both universal nonlattice conclusions. -/
def RealCorollaryStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ X : BanachModel.{0} ℝ,
    HasOneUnconditionalSchauderBasis ℝ X.Carrier ∧
    ∃ P : X.Carrier →L[ℝ] X.Carrier,
      P.comp P = P ∧ ‖P‖ < 1 + ρ ∧
      ¬ HasUnconditionalSchauderBasis ℝ P.range ∧
      ¬ HasUnconditionalSchauderBasis ℝ (P.range →L[ℝ] ℝ) ∧
      ¬ IsIsomorphicToRealBanachLattice P.range ∧
      ¬ IsIsomorphicToRealBanachLattice (P.range →L[ℝ] ℝ)

def ComplexCorollaryStatement : Prop := UnconditionalCorollaryStatement ℂ

/-- Concrete witnesses to the stated separable nonprimarity conclusion. -/
def SeparableNonprimarityStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ X : BanachModel.{0} ℝ,
    TopologicalSpace.SeparableSpace X.Carrier ∧
    HasRealBanachLatticeOrder X.Carrier ∧
    IsSuperreflexiveByRenorming ℝ X.Carrier ∧
    HasOneUnconditionalSchauderBasis ℝ X.Carrier ∧
    ∃ P : X.Carrier →L[ℝ] X.Carrier,
      P.comp P = P ∧ ‖P‖ < 1 + ρ ∧
      ‖ContinuousLinearMap.id ℝ X.Carrier - P‖ < 1 + ρ ∧
      ¬ IsIsomorphicToRealBanachLattice P.range ∧
      ¬ IsIsomorphicToRealBanachLattice
        (ContinuousLinearMap.id ℝ X.Carrier - P).range

end ComplementedSubspace
