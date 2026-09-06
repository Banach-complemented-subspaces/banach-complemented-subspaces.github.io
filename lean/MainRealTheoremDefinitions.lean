import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Tactic.NormNum

noncomputable section

open scoped ENNReal NNReal Topology

namespace ComplementedSubspace

-- Defined in this project: ComplementedSubspace/LocalUnconditional.lean
def basisMultiplier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (θ : Fin n → ℝ) : E →L[ℝ] E :=
  b.constrL (fun i => θ i • b i)

def unconditionalBasisConstant {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E) : ℝ≥0∞ :=
  max 1 (⨆ (θ : Fin n → ℝ) (_ : ∀ i, ‖θ i‖ ≤ 1), ‖basisMultiplier b θ‖ₑ)

def unconditionalConstant (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : ℝ≥0∞ :=
  ⨅ (n : ℕ) (b : Module.Basis (Fin n) ℝ E), unconditionalBasisConstant b

def lambdaDPR (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (V : Submodule ℝ Z) : ℝ≥0∞ :=
  ⨅ (F : Submodule ℝ Z) (_ : V ≤ F) (_ : FiniteDimensional ℝ ↥F),
    unconditionalConstant ↥F

def chiDPR (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] : ℝ≥0∞ :=
  ⨆ (V : Submodule ℝ Z) (_ : FiniteDimensional ℝ ↥V) (_ : V ≠ ⊥),
    lambdaDPR Z V

-- Defined in this project: ComplementedSubspace/LocalUnconditional.lean
structure GLFactorization {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (V : Submodule ℝ Z) where
  dimension : ℕ
  auxNorm : Seminorm ℝ (Fin dimension → ℝ)
  positive_definite : ∀ x, auxNorm x = 0 → x = 0
  unconditional : ∀ (θ x : Fin dimension → ℝ),
    (∀ i, ‖θ i‖ ≤ 1) → auxNorm (fun i => θ i * x i) ≤ auxNorm x
  a : ↥V →ₗ[ℝ] (Fin dimension → ℝ)
  b : (Fin dimension → ℝ) →ₗ[ℝ] Z
  factorizes : b.comp a = V.subtype
  aBound : ℝ≥0
  bBound : ℝ≥0
  bound_a : ∀ x : ↥V, auxNorm (a x) ≤ (aBound : ℝ) * ‖x‖
  bound_b : ∀ x : Fin dimension → ℝ, ‖b x‖ ≤ (bBound : ℝ) * auxNorm x

def GLFactorization.cost {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {V : Submodule ℝ Z} (F : GLFactorization V) : ℝ≥0∞ :=
  (F.aBound : ℝ≥0∞) * (F.bBound : ℝ≥0∞)

def lambdaGL (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (V : Submodule ℝ Z) : ℝ≥0∞ :=
  ⨅ F : GLFactorization V, F.cost

def chiGL (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] : ℝ≥0∞ :=
  ⨆ (V : Submodule ℝ Z) (_ : FiniteDimensional ℝ ↥V) (_ : V ≠ ⊥),
    lambdaGL Z V

-- Defined in this project: ComplementedSubspace/Ambient.lean
structure BlockParameters where
  dimension : ℕ → ℕ+
  exponent : ℕ → ℝ
  two_lt_exponent : ∀ j, 2 < exponent j
  exponent_le_three : ∀ j, exponent j ≤ 3
  exponent_antitone : Antitone exponent
  exponent_tendsto : Filter.Tendsto exponent Filter.atTop (𝓝 2)

instance (a : BlockParameters) (j : ℕ) :
    Fact (1 ≤ ENNReal.ofReal (a.exponent j)) := by
  constructor
  have h : (1 : ℝ) ≤ a.exponent j :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (a.two_lt_exponent j).le
  simpa using ENNReal.ofReal_le_ofReal h

abbrev Block (a : BlockParameters) (j : ℕ) :=
  PiLp (ENNReal.ofReal (a.exponent j)) (fun _ : Fin (a.dimension j) => ℝ)

-- Defined in this project: ComplementedSubspace/Ambient.lean
abbrev Ambient (a : BlockParameters) := lp (Block a) 2

-- Defined in this project: ComplementedSubspace/TheoremStatement.lean
def HasRealBanachLatticeOrder (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] : Prop :=
  ∃ latticeOrder : Lattice X,
    letI : Lattice X := latticeOrder
    IsOrderedAddMonoid X ∧ PosSMulMono ℝ X ∧ HasSolidNorm X

def HasSeparatedRange {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : X →L[ℝ] X) : Prop :=
  chiGL ↥P.range ≤ ‖P‖ₑ ∧
  chiDPR ↥P.range = ⊤ ∧
  chiGL (↥P.range →L[ℝ] ℝ) ≤ ‖P‖ₑ ∧
  chiDPR (↥P.range →L[ℝ] ℝ) = ⊤

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
