import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Real local unconditional structure

Definitions from `1a-Preliminaries.tex` of the supplied manuscript.

The unconditional basis constant uses all real coordinate multipliers of
modulus at most one, not merely coordinate projections. All infima and suprema
take values in `ℝ≥0∞`; consequently an empty infimum is infinity and no
attainment of an infimum is asserted. We use the harmless convention `u(0) = 1`
when defining the unconditional constant of the zero dimensional space.

For the Gordon--Lewis constant we represent the auxiliary finite dimensional
space on `Fin n → ℝ`, with an arbitrary positive-definite real seminorm as its
norm. A factorisation includes certified bounds for its two maps; the infimum
runs over all these bounds. This is the coordinate version of the manuscript's
definition with arbitrary finite dimensional Banach spaces and operator norms:
one transports a chosen 1-unconditional basis to coordinates and pulls back
the norm. `GLFactorization.ofUnconditionalBasis` implements this direction and
preserves the exact product of operator norms. Conversely the norm axioms below
give the actual finite dimensional Banach space `GLFactorization.Aux`.
`auxBasis_unconditional`, `auxA`, `auxB`, `aux_factorizes`, and
`aux_cost_le` implement the converse with no increase of the factorisation
cost. Thus the coordinate presentation has transport maps in both directions;
no quantification over a proper class of all normed spaces is needed. No main
theorem is assumed as an axiom.

The zero subspace is excluded from both outer suprema, exactly as in the
manuscript. The definitions also make sense for a normed space without a
completeness hypothesis; applications concern Banach spaces.
-/

noncomputable section

open scoped ENNReal NNReal

namespace ComplementedSubspace

section BasisConstants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coordinate multiplier of a finite real basis. Its value on `b i` is
`θ i • b i`; `constrL` supplies its continuity from finite dimensionality. -/
def basisMultiplier {n : ℕ} (b : Module.Basis (Fin n) ℝ E)
    (θ : Fin n → ℝ) : E →L[ℝ] E :=
  b.constrL (fun i => θ i • b i)

@[simp]
theorem basisMultiplier_apply_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) (θ : Fin n → ℝ) (i : Fin n) :
    basisMultiplier b θ (b i) = θ i • b i := by
  change b.constr ℝ (fun j => θ j • b j) (b i) = _
  exact b.constr_basis ℝ _ i

/-- The unconditional constant of a specified finite real basis. The maximum
with one incorporates the manuscript's convention that constants are ≥ 1. -/
def unconditionalBasisConstant {n : ℕ} (b : Module.Basis (Fin n) ℝ E) : ℝ≥0∞ :=
  max 1 (⨆ (θ : Fin n → ℝ) (_ : ∀ i, ‖θ i‖ ≤ 1), ‖basisMultiplier b θ‖ₑ)

theorem one_le_unconditionalBasisConstant {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) :
    1 ≤ unconditionalBasisConstant b :=
  le_max_left _ _

/-- The definition controls each admissible multiplier individually. -/
theorem enorm_basisMultiplier_le {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) (θ : Fin n → ℝ)
    (hθ : ∀ i, ‖θ i‖ ≤ 1) :
    ‖basisMultiplier b θ‖ₑ ≤ unconditionalBasisConstant b := by
  apply le_trans _ (le_max_right _ _)
  exact le_iSup_of_le θ (le_iSup_of_le hθ le_rfl)

/-- A basis with unconditional constant at most one gives contractions for
every admissible multiplier. -/
theorem norm_basisMultiplier_apply_le {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E)
    (hb : unconditionalBasisConstant b ≤ 1) (θ : Fin n → ℝ)
    (hθ : ∀ i, ‖θ i‖ ≤ 1) (x : E) :
    ‖basisMultiplier b θ x‖ ≤ ‖x‖ := by
  have he : ‖basisMultiplier b θ‖ₑ ≤ 1 := (enorm_basisMultiplier_le b θ hθ).trans hb
  have hn : ‖basisMultiplier b θ‖₊ ≤ (1 : ℝ≥0) :=
    enorm_le_coe.mp (by simpa only [ENNReal.coe_one] using he)
  have hr : ‖basisMultiplier b θ‖ ≤ (1 : ℝ) := by
    exact NNReal.coe_le_coe.mpr hn
  calc
    ‖basisMultiplier b θ x‖ ≤ ‖basisMultiplier b θ‖ * ‖x‖ :=
      (basisMultiplier b θ).le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- Coordinate reconstruction commutes with the corresponding basis
multiplier. This is the identity used in transporting auxiliary GL norms. -/
theorem basisMultiplier_equivFun_symm {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) (θ x : Fin n → ℝ) :
    basisMultiplier b θ (b.equivFun.symm x) =
      b.equivFun.symm (fun i => θ i * x i) := by
  change b.constr ℝ (fun i => θ i • b i) (b.equivFun.symm x) = _
  rw [Module.Basis.constr_apply_fintype, b.equivFun.apply_symm_apply,
    b.equivFun_symm_apply]
  simp only [smul_smul, mul_comm]

/-- `u(E)`: infimum of unconditional basis constants over all finite bases.
It is infinity when no finite basis exists. -/
def unconditionalConstant (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : ℝ≥0∞ :=
  ⨅ (n : ℕ) (b : Module.Basis (Fin n) ℝ E), unconditionalBasisConstant b

theorem one_le_unconditionalConstant (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : 1 ≤ unconditionalConstant E := by
  exact le_iInf fun n => le_iInf fun b => one_le_unconditionalBasisConstant b

end BasisConstants

section DPR

variable (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Local DPR constant at `V`: infimum of `u(F)` over finite dimensional
subspaces of the SAME ambient space containing `V`. -/
def lambdaDPR (V : Submodule ℝ Z) : ℝ≥0∞ :=
  ⨅ (F : Submodule ℝ Z) (_ : V ≤ F) (_ : FiniteDimensional ℝ ↥F),
    unconditionalConstant ↥F

/-- Dubinsky--Pełczyński--Rosenthal local unconditional structure constant. -/
def chiDPR : ℝ≥0∞ :=
  ⨆ (V : Submodule ℝ Z) (_ : FiniteDimensional ℝ ↥V) (_ : V ≠ ⊥),
    lambdaDPR Z V

theorem lambdaDPR_le_of_le {V F : Submodule ℝ Z}
    (hVF : V ≤ F) (hF : FiniteDimensional ℝ ↥F) :
    lambdaDPR Z V ≤ unconditionalConstant ↥F := by
  exact iInf_le_of_le F (iInf_le_of_le hVF (iInf_le_of_le hF le_rfl))

theorem one_le_lambdaDPR (V : Submodule ℝ Z) : 1 ≤ lambdaDPR Z V := by
  exact le_iInf fun F => le_iInf fun _ => le_iInf fun _ =>
    one_le_unconditionalConstant ↥F

/-- Finiteness, rather than the existence of an optimal witness, defines
the DPR local unconditional structure property. -/
def HasDPRLocalUnconditionalStructure : Prop := chiDPR Z < ⊤

end DPR

section GordonLewis

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A genuine finite dimensional Gordon--Lewis factorisation, presented on
coordinates with an arbitrary norm. `b` is NOT required to be injective.

The norm is a positive-definite `Seminorm`, so its triangle inequality,
homogeneity and nonnegativity are already supplied by mathlib. The coordinate
basis is 1-unconditional by the displayed contraction condition. -/
structure GLFactorization (V : Submodule ℝ Z) where
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

/-- The product of certified operator bounds of a GL factorisation. -/
def GLFactorization.cost {V : Submodule ℝ Z} (F : GLFactorization V) : ℝ≥0∞ :=
  (F.aBound : ℝ≥0∞) * (F.bBound : ℝ≥0∞)

@[simp]
theorem GLFactorization.factorizes_apply {V : Submodule ℝ Z}
    (F : GLFactorization V) (x : ↥V) : F.b (F.a x) = (x : Z) :=
  congrArg (fun T : ↥V →ₗ[ℝ] Z => T x) F.factorizes

/-- Injectivity of the first map is a consequence of factorisation, not an
additional condition on the auxiliary space. -/
theorem GLFactorization.a_injective {V : Submodule ℝ Z}
    (F : GLFactorization V) : Function.Injective F.a := by
  intro x y h
  apply Subtype.ext
  calc
    (x : Z) = F.b (F.a x) := (F.factorizes_apply x).symm
    _ = F.b (F.a y) := congrArg F.b h
    _ = (y : Z) := F.factorizes_apply y

/-- The two certified bounds control their composite, which is the inclusion. -/
theorem GLFactorization.norm_le_bound_mul {V : Submodule ℝ Z}
    (F : GLFactorization V) (x : ↥V) :
    ‖x‖ ≤ ((F.bBound : ℝ) * (F.aBound : ℝ)) * ‖x‖ := by
  calc
    ‖x‖ = ‖F.b (F.a x)‖ := by rw [F.factorizes_apply]; rfl
    _ ≤ (F.bBound : ℝ) * F.auxNorm (F.a x) := F.bound_b (F.a x)
    _ ≤ (F.bBound : ℝ) * ((F.aBound : ℝ) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (F.bound_a x) F.bBound.2
    _ = ((F.bBound : ℝ) * (F.aBound : ℝ)) * ‖x‖ := (mul_assoc _ _ _).symm

/-- A factorisation of a nonzero inclusion cannot have cost below one. -/
theorem GLFactorization.one_le_cost {V : Submodule ℝ Z} [Nontrivial ↥V]
    (F : GLFactorization V) : 1 ≤ F.cost := by
  obtain ⟨x, hx⟩ := exists_ne (0 : ↥V)
  have hreal : (1 : ℝ) ≤ (F.bBound : ℝ) * (F.aBound : ℝ) :=
    le_of_mul_le_mul_right (by simpa only [one_mul] using F.norm_le_bound_mul x)
      (norm_pos_iff.mpr hx)
  have hnn : (1 : ℝ≥0) ≤ F.aBound * F.bBound := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_one, NNReal.coe_mul, mul_comm] using hreal
  simpa only [GLFactorization.cost, ENNReal.coe_one, ENNReal.coe_mul] using
    (ENNReal.coe_le_coe.mpr hnn)

/-- Transport an actual factorisation through an arbitrary finite dimensional
normed space with a 1-unconditional basis to the coordinate presentation.
The stored bounds are EXACTLY the operator norms of its two maps. -/
def GLFactorization.ofUnconditionalBasis {V : Submodule ℝ Z}
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n : ℕ} (e : Module.Basis (Fin n) ℝ U)
    (he : unconditionalBasisConstant e ≤ 1)
    (a : ↥V →L[ℝ] U) (b : U →L[ℝ] Z)
    (h : b.comp a = V.subtypeL) : GLFactorization V where
  dimension := n
  auxNorm := (normSeminorm ℝ U).comp e.equivFun.symm.toLinearMap
  positive_definite := by
    intro x hx
    change ‖e.equivFun.symm x‖ = 0 at hx
    apply e.equivFun.symm.injective
    simpa only [map_zero] using norm_eq_zero.mp hx
  unconditional := by
    intro θ x hθ
    change ‖e.equivFun.symm (fun i => θ i * x i)‖ ≤ ‖e.equivFun.symm x‖
    rw [← basisMultiplier_equivFun_symm]
    exact norm_basisMultiplier_apply_le e he θ hθ _
  a := e.equivFun.toLinearMap.comp a.toLinearMap
  b := b.toLinearMap.comp e.equivFun.symm.toLinearMap
  factorizes := by
    ext x
    change b (e.equivFun.symm (e.equivFun (a x))) = (x : Z)
    rw [e.equivFun.symm_apply_apply]
    exact congrArg (fun T : ↥V →L[ℝ] Z => T x) h
  aBound := ‖a‖₊
  bBound := ‖b‖₊
  bound_a := by
    intro x
    change ‖e.equivFun.symm (e.equivFun (a x))‖ ≤ ‖a‖ * ‖x‖
    rw [e.equivFun.symm_apply_apply]
    exact a.le_opNorm x
  bound_b := by
    intro x
    exact b.le_opNorm (e.equivFun.symm x)

@[simp]
theorem GLFactorization.ofUnconditionalBasis_cost {V : Submodule ℝ Z}
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n : ℕ} (e : Module.Basis (Fin n) ℝ U)
    (he : unconditionalBasisConstant e ≤ 1)
    (a : ↥V →L[ℝ] U) (b : U →L[ℝ] Z)
    (h : b.comp a = V.subtypeL) :
    (GLFactorization.ofUnconditionalBasis e he a b h).cost =
      (‖a‖₊ : ℝ≥0∞) * (‖b‖₊ : ℝ≥0∞) := rfl

namespace GLFactorization

variable {V : Submodule ℝ Z} (F : GLFactorization V)

/-- A fresh type synonym carries the particular auxiliary norm of `F`, rather
than the default supremum norm on finite coordinate vectors. -/
def Aux := Fin F.dimension → ℝ

instance auxAddCommGroup : AddCommGroup F.Aux :=
  inferInstanceAs (AddCommGroup (Fin F.dimension → ℝ))

instance auxModule : Module ℝ F.Aux :=
  inferInstanceAs (Module ℝ (Fin F.dimension → ℝ))

/-- Positive definiteness upgrades the stored seminorm to an additive norm. -/
def auxAddGroupNorm : AddGroupNorm F.Aux where
  toAddGroupSeminorm := F.auxNorm.toAddGroupSeminorm
  eq_zero_of_map_eq_zero' := F.positive_definite

instance auxNormedAddCommGroup : NormedAddCommGroup F.Aux :=
  F.auxAddGroupNorm.toNormedAddCommGroup

instance auxNormedSpace : NormedSpace ℝ F.Aux where
  norm_smul_le c x := (F.auxNorm.smul' c x).le

instance auxFiniteDimensional : FiniteDimensional ℝ F.Aux :=
  inferInstanceAs (FiniteDimensional ℝ (Fin F.dimension → ℝ))

instance auxCompleteSpace : CompleteSpace F.Aux :=
  FiniteDimensional.complete ℝ F.Aux

@[simp]
theorem aux_norm (x : F.Aux) : ‖x‖ = F.auxNorm x := rfl

/-- The coordinate basis of the actual auxiliary Banach space. -/
def auxBasis : Module.Basis (Fin F.dimension) ℝ F.Aux :=
  Pi.basisFun ℝ (Fin F.dimension)

theorem auxBasis_multiplier_apply (θ : Fin F.dimension → ℝ) (x : F.Aux) :
    basisMultiplier F.auxBasis θ x = fun i => θ i * x i := by
  have h := basisMultiplier_equivFun_symm F.auxBasis θ x
  have he : F.auxBasis.equivFun = LinearEquiv.refl ℝ F.Aux :=
    Pi.basisFun_equivFun ℝ (Fin F.dimension)
  rw [he] at h
  exact h

/-- The canonical coordinate basis really has unconditional constant at most
one in the actual auxiliary normed space. -/
theorem auxBasis_unconditional : unconditionalBasisConstant F.auxBasis ≤ 1 := by
  apply max_le le_rfl
  refine iSup_le fun θ => iSup_le fun hθ => ?_
  have hn : ‖basisMultiplier F.auxBasis θ‖ ≤ (1 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [F.auxBasis_multiplier_apply, one_mul]
    exact F.unconditional θ x hθ
  have hn' : ‖basisMultiplier F.auxBasis θ‖₊ ≤ (1 : ℝ≥0) :=
    NNReal.coe_le_coe.mp hn
  exact enorm_le_coe.mpr hn'

/-- The first map is continuous for the actual auxiliary norm. -/
def auxA : ↥V →L[ℝ] F.Aux :=
  (show ↥V →ₗ[ℝ] F.Aux from F.a).mkContinuous (F.aBound : ℝ) F.bound_a

/-- The second map is continuous for the actual auxiliary norm. -/
def auxB : F.Aux →L[ℝ] Z :=
  (show F.Aux →ₗ[ℝ] Z from F.b).mkContinuous (F.bBound : ℝ) F.bound_b

theorem aux_factorizes : F.auxB.comp F.auxA = V.subtypeL := by
  ext x
  exact F.factorizes_apply x

theorem norm_auxA_le : ‖F.auxA‖ ≤ (F.aBound : ℝ) :=
  F.auxA.opNorm_le_bound F.aBound.2 F.bound_a

theorem norm_auxB_le : ‖F.auxB‖ ≤ (F.bBound : ℝ) :=
  F.auxB.opNorm_le_bound F.bBound.2 F.bound_b

/-- Realizing a coordinate witness as actual bounded operators does not
increase its cost. Together with `ofUnconditionalBasis_cost` this justifies
using certified bounds in the infimum. -/
theorem aux_cost_le :
    (‖F.auxA‖₊ : ℝ≥0∞) * (‖F.auxB‖₊ : ℝ≥0∞) ≤ F.cost := by
  have ha : ‖F.auxA‖₊ ≤ F.aBound := NNReal.coe_le_coe.mp F.norm_auxA_le
  have hb : ‖F.auxB‖₊ ≤ F.bBound := NNReal.coe_le_coe.mp F.norm_auxB_le
  exact mul_le_mul' (ENNReal.coe_le_coe.mpr ha) (ENNReal.coe_le_coe.mpr hb)

end GLFactorization

variable (Z)

/-- Local Gordon--Lewis constant in the coordinate presentation documented
above. Every admissible factorisation and every admissible bound is included. -/
def lambdaGL (V : Submodule ℝ Z) : ℝ≥0∞ :=
  ⨅ F : GLFactorization V, F.cost

/-- Gordon--Lewis local unconditional structure constant, using arbitrary
finite dimensional auxiliary norms and excluding the zero initial subspace. -/
def chiGL : ℝ≥0∞ :=
  ⨆ (V : Submodule ℝ Z) (_ : FiniteDimensional ℝ ↥V) (_ : V ≠ ⊥),
    lambdaGL Z V

theorem lambdaGL_le_cost {V : Submodule ℝ Z} (F : GLFactorization V) :
    lambdaGL Z V ≤ F.cost :=
  iInf_le _ F

theorem one_le_lambdaGL (V : Submodule ℝ Z) [Nontrivial ↥V] :
    1 ≤ lambdaGL Z V :=
  le_iInf fun F => F.one_le_cost

/-- Finiteness of the Gordon--Lewis local unconditional structure constant. -/
def HasGLLocalUnconditionalStructure : Prop := chiGL Z < ⊤

end GordonLewis

end ComplementedSubspace
