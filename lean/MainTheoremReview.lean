import ComplementedSubspace.TheoremStatement

/-!
# Real main theorem: definitions and statement for human review

The main theorem is proved by `ComplementedSubspace.realMainTheorem` in
`ComplementedSubspace/RealMainTheorem.lean`. This review file displays aliases
of the definitions and statement. Its final example only checks definitional
equality with the target; the proof of the target lives in the separate module.

Scalars are REAL throughout. All norms are the actual inherited or operator
norms. Constants take values in ℝ≥0∞, so ⊤ means infinity.

`basisMultiplier b θ` is the continuous linear map taking b i to θ i • b i.
The bounds below use ALL real multipliers |θ i| ≤ 1, not only projections.
-/

noncomputable section
open scoped ENNReal NNReal
open ComplementedSubspace

namespace MainTheoremReview

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unconditional constant of a specified finite basis; the zero-space
convention is one. -/
def basisConstant {n : ℕ} (b : Module.Basis (Fin n) ℝ E) : ℝ≥0∞ :=
  max 1 (⨆ (θ : Fin n → ℝ) (_ : ∀ i, ‖θ i‖ ≤ 1), ‖basisMultiplier b θ‖ₑ)

/-- u(E): infimum over all finite bases, with the existing norm on E. -/
def u (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : ℝ≥0∞ :=
  ⨅ (n : ℕ) (b : Module.Basis (Fin n) ℝ E), basisConstant b

/-- Exact finite superspaces inside the SAME ambient E. -/
def localDPR (V : Submodule ℝ E) : ℝ≥0∞ :=
  ⨅ (F : Submodule ℝ E) (_ : V ≤ F) (_ : FiniteDimensional ℝ F), u F

/-- The zero subspace is excluded from the outer supremum. -/
def dpr (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : ℝ≥0∞ :=
  ⨆ (V : Submodule ℝ E) (_ : FiniteDimensional ℝ V) (_ : V ≠ ⊥), localDPR V

/-
GLFactorization V is the following genuine finite-dimensional factorization:

  dimension : ℕ
  auxNorm : Seminorm ℝ (Fin dimension → ℝ)
  positive_definite : ∀ x, auxNorm x = 0 → x = 0
  unconditional : ∀ θ x, (∀ i, ‖θ i‖ ≤ 1) →
    auxNorm (fun i => θ i * x i) ≤ auxNorm x
  a : V →ₗ[ℝ] (Fin dimension → ℝ)
  b : (Fin dimension → ℝ) →ₗ[ℝ] E
  factorizes : b.comp a = V.subtype
  aBound bBound : ℝ≥0
  bound_a : ∀ x : V, auxNorm (a x) ≤ aBound * ‖x‖
  bound_b : ∀ x, ‖b x‖ ≤ bBound * auxNorm x

Its cost is aBound * bBound. The auxiliary norm is arbitrary, positive definite,
and 1-unconditional. The map b need not be injective. Infima over all certified
bounds recover operator-norm costs. Transport to and from ordinary finite
Banach-space factorizations is already proved in LocalUnconditional.lean.
-/

def localGL (V : Submodule ℝ E) : ℝ≥0∞ :=
  ⨅ F : GLFactorization V, F.cost

def gl (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : ℝ≥0∞ :=
  ⨆ (V : Submodule ℝ E) (_ : FiniteDimensional ℝ V) (_ : V ≠ ⊥), localGL V

-- These equalities check that the displayed definitions are the actual ones.
example : dpr E = chiDPR E := rfl
example : gl E = chiGL E := rfl

/-
BlockParameters records:
  positive finite dimensions N j;
  real exponents 2 < p j ≤ 3;
  p is antitone and tends to 2.

Block a j = PiLp (ENNReal.ofReal (a.exponent j))
  (fun _ : Fin (a.dimension j) => ℝ)
Ambient a = lp (Block a) 2.

These use COUNTING norms, and are actual complete normed spaces.

HasRealBanachLatticeOrder X means that there exists a lattice order compatible
with the existing addition and positive real scalar multiplication, and with
solid norm: |x| ≤ |y| implies ‖x‖ ≤ ‖y‖. It preserves the existing norm.
-/

/-- All four conclusions for one range. The dual is the CONTINUOUS dual. -/
def separated (P : E →L[ℝ] E) : Prop :=
  gl P.range ≤ ‖P‖ₑ ∧
  dpr P.range = ⊤ ∧
  gl (P.range →L[ℝ] ℝ) ≤ ‖P‖ₑ ∧
  dpr (P.range →L[ℝ] ℝ) = ⊤

/-- The statement proved by `ComplementedSubspace.realMainTheorem`.

The manuscript says superreflexive. This target asks for the stronger property
that the constructed ambient's given norm is uniformly convex. The standard
superreflexivity characterization by equivalent uniformly convex renormability
is the intended convention; no finite-representability equivalence is asserted
as a proved Lean theorem here. This difference is explicit for review.
-/
def mainStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    ∃ a : BlockParameters,
      TopologicalSpace.SeparableSpace (Ambient a) ∧
      UniformConvexSpace (Ambient a) ∧
      HasRealBanachLatticeOrder (Ambient a) ∧
      ∃ P : Ambient a →L[ℝ] Ambient a,
        P.comp P = P ∧
        ‖P‖ < 1 + ρ ∧
        ‖ContinuousLinearMap.id ℝ (Ambient a) - P‖ < 1 + ρ ∧
        separated P ∧
        separated (ContinuousLinearMap.id ℝ (Ambient a) - P)

-- Equality of formulations only; the main proof is in RealMainTheorem.lean.
example : mainStatement = RealMainTheoremStatement := rfl

end MainTheoremReview
