import ComplementedSubspace.LocalUnconditional
import Mathlib.Basic.ENNReal.Inv

/-!
# Transport of Gordon--Lewis factorizations through a retraction

This is the factorization step in Lemma `lem:complemented-gl` of the supplied
manuscript. It does not assume that the GL infimum is attained. The auxiliary
norm and the auxiliary dimension are retained exactly. The two certified
operator bounds are multiplied by the norms of the embedding and retraction.

The theorem that the ambient space has GL constant one remains a separate
prerequisite. The passage to infima and suprema is included below.
-/

noncomputable section

open scoped NNReal ENNReal

namespace ComplementedSubspace

variable {Z X : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The map from a subspace to its image under a continuous linear map. -/
def retractionImageMap (J : Z →L[ℝ] X) (V : Submodule ℝ Z) :
    ↥V →ₗ[ℝ] ↥(V.map J.toLinearMap) :=
  (J.toLinearMap.comp V.subtype).codRestrict (V.map J.toLinearMap)
    (fun v => ⟨(v : Z), v.property, rfl⟩)

@[simp]
theorem retractionImageMap_coe (J : Z →L[ℝ] X) (V : Submodule ℝ Z) (v : V) :
    (retractionImageMap J V v : X) = J v :=
  rfl

/-- Pull back a GL factorization on the image subspace through a bounded
retraction `R ∘ J = id`. No injectivity assumption is imposed on its second
factor. -/
def GLFactorization.throughRetraction (J : Z →L[ℝ] X) (R : X →L[ℝ] Z)
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ Z)
    {V : Submodule ℝ Z} (F : GLFactorization (V.map J.toLinearMap)) :
    GLFactorization V where
  dimension := F.dimension
  auxNorm := F.auxNorm
  positive_definite := F.positive_definite
  unconditional := F.unconditional
  a := F.a.comp (retractionImageMap J V)
  b := R.toLinearMap.comp F.b
  factorizes := by
    ext v
    change R (F.b (F.a (retractionImageMap J V v))) = (v : Z)
    have hF := congrArg
      (fun f : ↥(V.map J.toLinearMap) →ₗ[ℝ] X => f (retractionImageMap J V v))
      F.factorizes
    change F.b (F.a (retractionImageMap J V v)) = J v at hF
    rw [hF]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun f : Z →L[ℝ] Z => f (v : Z)) hRJ
  aBound := F.aBound * ‖J‖₊
  bBound := ‖R‖₊ * F.bBound
  bound_a := by
    intro v
    change F.auxNorm (F.a (retractionImageMap J V v)) ≤
      ((F.aBound * ‖J‖₊ : ℝ≥0) : ℝ) * ‖v‖
    calc
      F.auxNorm (F.a (retractionImageMap J V v)) ≤
          (F.aBound : ℝ) * ‖retractionImageMap J V v‖ := F.bound_a _
      _ = (F.aBound : ℝ) * ‖J v‖ := rfl
      _ ≤ (F.aBound : ℝ) * (‖J‖ * ‖(v : Z)‖) :=
        mul_le_mul_of_nonneg_left (J.le_opNorm (v : Z)) F.aBound.property
      _ = ((F.aBound * ‖J‖₊ : ℝ≥0) : ℝ) * ‖v‖ := by
        simp only [NNReal.coe_mul, coe_nnnorm, mul_assoc, Submodule.norm_coe]
  bound_b := by
    intro x
    change ‖R (F.b x)‖ ≤ ((‖R‖₊ * F.bBound : ℝ≥0) : ℝ) * F.auxNorm x
    calc
      ‖R (F.b x)‖ ≤ ‖R‖ * ‖F.b x‖ := R.le_opNorm _
      _ ≤ ‖R‖ * ((F.bBound : ℝ) * F.auxNorm x) :=
        mul_le_mul_of_nonneg_left (F.bound_b x) (norm_nonneg R)
      _ = ((‖R‖₊ * F.bBound : ℝ≥0) : ℝ) * F.auxNorm x := by
        simp only [NNReal.coe_mul, coe_nnnorm, mul_assoc]

/-- The transported cost is the original cost multiplied by the product of
the two retraction norms. This is the quantitative estimate used in the paper. -/
theorem GLFactorization.throughRetraction_cost (J : Z →L[ℝ] X) (R : X →L[ℝ] Z)
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ Z)
    {V : Submodule ℝ Z} (F : GLFactorization (V.map J.toLinearMap)) :
    (F.throughRetraction J R hRJ).cost = ‖J‖ₑ * ‖R‖ₑ * F.cost := by
  simp only [GLFactorization.cost, GLFactorization.throughRetraction, ENNReal.coe_mul,
    enorm_eq_nnnorm, mul_assoc, mul_comm, mul_left_comm]

/-- Every GL factorization of the image gives this upper bound on the original
local GL constant. There is no selection of an optimal factorization. -/
theorem lambdaGL_le_retraction_cost (J : Z →L[ℝ] X) (R : X →L[ℝ] Z)
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ Z)
    {V : Submodule ℝ Z} (F : GLFactorization (V.map J.toLinearMap)) :
    lambdaGL Z V ≤ ‖J‖ₑ * ‖R‖ₑ * F.cost := by
  rw [← F.throughRetraction_cost J R hRJ]
  exact lambdaGL_le_cost Z (F.throughRetraction J R hRJ)

/-- A retraction of a nonzero normed space has product of operator norms at
least one. -/
theorem one_le_retraction_norm_product [Nontrivial Z]
    (J : Z →L[ℝ] X) (R : X →L[ℝ] Z)
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ Z) :
    1 ≤ ‖R‖ * ‖J‖ := by
  have h := R.opNorm_comp_le J
  rwa [hRJ, ContinuousLinearMap.norm_id] at h

/-- Quantitative transport of the local infimum through a bounded retraction.
An optimal factorization is not required to exist. -/
theorem lambdaGL_le_of_retraction [Nontrivial Z]
    (J : Z →L[ℝ] X) (R : X →L[ℝ] Z)
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ Z) (V : Submodule ℝ Z) :
    lambdaGL Z V ≤ ‖J‖ₑ * ‖R‖ₑ * lambdaGL X (V.map J.toLinearMap) := by
  have hnorm := one_le_retraction_norm_product J R hRJ
  have hJ : J ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero, mul_zero] at hnorm
    exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) hnorm
  have hR : R ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero, zero_mul] at hnorm
    exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) hnorm
  have hc0 : ‖J‖ₑ * ‖R‖ₑ ≠ 0 :=
    mul_ne_zero
      (by
        change (‖J‖₊ : ℝ≥0∞) ≠ 0
        exact ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr hJ))
      (by
        change (‖R‖₊ : ℝ≥0∞) ≠ 0
        exact ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr hR))
  have hctop : ‖J‖ₑ * ‖R‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp [enorm_eq_nnnorm]) (by simp [enorm_eq_nnnorm])
  change lambdaGL Z V ≤ (‖J‖ₑ * ‖R‖ₑ) *
    ⨅ F : GLFactorization (V.map J.toLinearMap), F.cost
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  exact le_iInf fun F => lambdaGL_le_retraction_cost J R hRJ F

/-- Gordon--Lewis local unconditional structure passes to a complemented
subspace, quantitatively. This statement works for any bounded retraction
and any ambient GL constant. -/
theorem chiGL_le_of_retraction [Nontrivial Z]
    (J : Z →L[ℝ] X) (R : X →L[ℝ] Z)
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ Z) :
    chiGL Z ≤ ‖J‖ₑ * ‖R‖ₑ * chiGL X := by
  have hleft : Function.LeftInverse R J := fun z => by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun f : Z →L[ℝ] Z => f z) hRJ
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hV0 => ?_
  letI : FiniteDimensional ℝ ↥V := hV
  have hJV : FiniteDimensional ℝ ↥(V.map J.toLinearMap) := inferInstance
  have hJV0 : V.map J.toLinearMap ≠ ⊥ := by
    intro hzero
    apply hV0
    apply Submodule.map_injective_of_injective (f := J.toLinearMap) hleft.injective
    simpa only [Submodule.map_bot] using hzero
  apply (lambdaGL_le_of_retraction J R hRJ V).trans
  apply mul_le_mul' le_rfl
  exact le_iSup_of_le (V.map J.toLinearMap)
    (le_iSup_of_le hJV (le_iSup_of_le hJV0 le_rfl))

/-- Specialization used by the manuscript: an ambient GL constant at most one
gives the product-of-norms estimate on the complemented space. -/
theorem chiGL_le_norm_product_of_retraction [Nontrivial Z]
    (J : Z →L[ℝ] X) (R : X →L[ℝ] Z)
    (hRJ : R.comp J = ContinuousLinearMap.id ℝ Z) (hX : chiGL X ≤ 1) :
    chiGL Z ≤ ‖J‖ₑ * ‖R‖ₑ := by
  calc
    chiGL Z ≤ ‖J‖ₑ * ‖R‖ₑ * chiGL X := chiGL_le_of_retraction J R hRJ
    _ ≤ ‖J‖ₑ * ‖R‖ₑ * 1 := mul_le_mul' le_rfl hX
    _ = ‖J‖ₑ * ‖R‖ₑ := mul_one _

/-- The projection, restricted to its range as codomain, is a left inverse
to the range inclusion. The range has the inherited norm. -/
theorem projection_range_retraction (P : X →L[ℝ] X) (hP : P.comp P = P) :
    P.rangeRestrict.comp P.range.subtypeL = ContinuousLinearMap.id ℝ ↥P.range := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  change P (v : X) = (v : X)
  obtain ⟨x, hx⟩ := v.property
  rw [← hx]
  change P (P x) = P x
  exact congrArg (fun T : X →L[ℝ] X => T x) hP

/-- Restricting an operator's codomain to its range does not change its norm. -/
theorem norm_rangeRestrict (P : X →L[ℝ] X) : ‖P.rangeRestrict‖ = ‖P‖ := by
  apply le_antisymm
  · exact P.rangeRestrict.opNorm_le_bound (norm_nonneg P) fun x => P.le_opNorm x
  · exact P.opNorm_le_bound (norm_nonneg P.rangeRestrict) fun x =>
      P.rangeRestrict.le_opNorm x

/-- The precise projection estimate used in the main theorem, conditional only
on the ambient GL constant being at most one. -/
theorem chiGL_range_le_projection_norm (P : X →L[ℝ] X) [Nontrivial ↥P.range]
    (hP : P.comp P = P) (hX : chiGL X ≤ 1) : chiGL ↥P.range ≤ ‖P‖ₑ := by
  have h := chiGL_le_norm_product_of_retraction
    P.range.subtypeL P.rangeRestrict (projection_range_retraction P hP) hX
  have hinc : ‖P.range.subtypeL‖ₑ = 1 := by
    rw [← ofReal_norm, Submodule.norm_subtypeL, ENNReal.ofReal_one]
  have hres : ‖P.rangeRestrict‖ₑ = ‖P‖ₑ :=
    enorm_eq_iff_norm_eq.mpr (norm_rangeRestrict P)
  simpa only [hinc, hres, one_mul] using h

end ComplementedSubspace
