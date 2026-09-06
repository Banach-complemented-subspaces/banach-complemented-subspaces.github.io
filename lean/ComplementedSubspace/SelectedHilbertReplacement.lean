import ComplementedSubspace.LocalHilbert
import ComplementedSubspace.BasisTransport
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Replace only the selected tail by its nearby Hilbert norm

The first summand retains its original Banach norm. The exact square-norm
decomposition makes replacement by a smaller tail norm contractive, and the
inverse has the same distortion as the tail Hilbert approximation.
-/

noncomputable section
open scoped ENNReal NNReal

namespace ComplementedSubspace

variable {Y E W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The second component, restricted to the selected finite span and its actual image. -/
def selectedTailMap (F : Submodule ℝ Y) (S : Y →L[ℝ] W) :
    F →L[ℝ] (F.map S.toLinearMap) :=
  (S.comp F.subtypeL).codRestrict _ (fun y => ⟨y, y.property, rfl⟩)

@[simp] theorem selectedTailMap_coe (F : Submodule ℝ Y) (S : Y →L[ℝ] W) (y : F) :
    (selectedTailMap F S y : W) = S y := rfl

theorem selectedTail_finrank_le (F : Submodule ℝ Y) [FiniteDimensional ℝ F]
    (S : Y →L[ℝ] W) :
    Module.finrank ℝ (F.map S.toLinearMap) ≤ Module.finrank ℝ F :=
  Submodule.finrank_map_le S.toLinearMap F

section Model

variable (F : Submodule ℝ Y) (R : Y →L[ℝ] E) (S : Y →L[ℝ] W)
  (p : HilbertNormModel (F.map S.toLinearMap)) (D : ℝ≥0)
  (hp : ∀ z : F.map S.toLinearMap, p.q z ≤ ‖z‖ ∧ ‖z‖ ≤ (D : ℝ) * p.q z)

/-- The concrete map `y ↦ (R y, J (S y))` into the Hilbertian two-term sum. -/
def selectedHilbertMap : F →L[ℝ] WithLp 2 (E × p.Space) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E p.Space).symm.toContinuousLinearMap.comp
    ((R.comp F.subtypeL).prod
      ((p.equivOfBounds (D : ℝ) hp).toContinuousLinearMap.comp (selectedTailMap F S)))

@[simp] theorem selectedHilbertMap_fst (y : F) :
    (selectedHilbertMap F R S p D hp y).fst = R y := rfl

theorem selectedHilbertMap_norm_sq (y : F) :
    ‖selectedHilbertMap F R S p D hp y‖ ^ 2 =
      ‖R y‖ ^ 2 + p.q (selectedTailMap F S y) ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

variable (hdec : ∀ y : Y, ‖y‖ ^ 2 = ‖R y‖ ^ 2 + ‖S y‖ ^ 2)
include hdec

theorem selectedHilbertMap_contracts (y : F) :
    ‖selectedHilbertMap F R S p D hp y‖ ≤ ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [selectedHilbertMap_norm_sq]
  have hq := (sq_le_sq₀ (apply_nonneg p.q _) (norm_nonneg (selectedTailMap F S y))).mpr
    (hp (selectedTailMap F S y)).1
  change ‖R y‖ ^ 2 + p.q (selectedTailMap F S y) ^ 2 ≤ ‖(y : Y)‖ ^ 2
  rw [hdec]
  exact add_le_add le_rfl hq

theorem norm_selectedHilbertMap_le_one : ‖selectedHilbertMap F R S p D hp‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simpa only [one_mul] using selectedHilbertMap_contracts F R S p D hp hdec y

variable (hD : 1 ≤ D)
include hD

theorem selectedHilbertMap_lower_bound (y : F) :
    ‖y‖ ≤ (D : ℝ) * ‖selectedHilbertMap F R S p D hp y‖ := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hq := (sq_le_sq₀ (norm_nonneg (selectedTailMap F S y))
    (mul_nonneg D.2 (apply_nonneg p.q _))).mpr (hp (selectedTailMap F S y)).2
  rw [mul_pow] at hq
  have hR : ‖R y‖ ^ 2 ≤ (D : ℝ) ^ 2 * ‖R y‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (D : ℝ) ^ 2 - 1 by nlinarith) (sq_nonneg ‖R y‖)]
  apply (sq_le_sq₀ (norm_nonneg y) (mul_nonneg D.2 (norm_nonneg _))).mp
  calc
    ‖y‖ ^ 2 = ‖R y‖ ^ 2 + ‖selectedTailMap F S y‖ ^ 2 := hdec y
    _ ≤ (D : ℝ) ^ 2 * ‖R y‖ ^ 2 + (D : ℝ) ^ 2 * p.q (selectedTailMap F S y) ^ 2 :=
      add_le_add hR hq
    _ = ((D : ℝ) * ‖selectedHilbertMap F R S p D hp y‖) ^ 2 := by
      rw [mul_pow, selectedHilbertMap_norm_sq]
      ring

theorem selectedHilbertMap_injective : Function.Injective (selectedHilbertMap F R S p D hp) := by
  intro x y hxy
  have hz : selectedHilbertMap F R S p D hp (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h := selectedHilbertMap_lower_bound F R S p D hp hdec hD (x - y)
  rw [hz, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- The image has the inherited two-term sum norm, with the explicit inverse bound. -/
def selectedHilbertEquiv : F ≃L[ℝ] (selectedHilbertMap F R S p D hp).range := by
  let e := LinearEquiv.ofInjective (selectedHilbertMap F R S p D hp).toLinearMap
    (selectedHilbertMap_injective F R S p D hp hdec hD)
  exact e.toContinuousLinearEquivOfBounds 1 D
    (fun y => by
      change ‖selectedHilbertMap F R S p D hp y‖ ≤ 1 * ‖y‖
      simpa only [one_mul] using selectedHilbertMap_contracts F R S p D hp hdec y)
    (fun y => by
      have hy : selectedHilbertMap F R S p D hp (e.symm y) = (y : WithLp 2 (E × p.Space)) :=
        congrArg Subtype.val (e.apply_symm_apply y)
      simpa only [hy, Submodule.norm_coe] using
        selectedHilbertMap_lower_bound F R S p D hp hdec hD (e.symm y))

@[simp] theorem selectedHilbertEquiv_coe (y : F) :
    (selectedHilbertEquiv F R S p D hp hdec hD y : WithLp 2 (E × p.Space)) =
      selectedHilbertMap F R S p D hp y := rfl

theorem selectedHilbertEquiv_contracts (y : F) :
    ‖selectedHilbertEquiv F R S p D hp hdec hD y‖ ≤ ‖y‖ :=
  selectedHilbertMap_contracts F R S p D hp hdec y

theorem selectedHilbertEquiv_symm_bound
    (y : (selectedHilbertMap F R S p D hp).range) :
    ‖(selectedHilbertEquiv F R S p D hp hdec hD).symm y‖ ≤ (D : ℝ) * ‖y‖ := by
  let e := selectedHilbertEquiv F R S p D hp hdec hD
  change ‖e.symm y‖ ≤ (D : ℝ) * ‖y‖
  have hy : selectedHilbertMap F R S p D hp (e.symm y) = (y : WithLp 2 (E × p.Space)) :=
    (selectedHilbertEquiv_coe F R S p D hp hdec hD (e.symm y)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply y))
  simpa only [hy, Submodule.norm_coe] using
    selectedHilbertMap_lower_bound F R S p D hp hdec hD (e.symm y)

theorem selectedHilbertRange_finrank [FiniteDimensional ℝ F] :
    Module.finrank ℝ (selectedHilbertMap F R S p D hp).range = Module.finrank ℝ F :=
  (selectedHilbertEquiv F R S p D hp hdec hD).toLinearEquiv.finrank_eq.symm

theorem selectedHilbertBasis_constant_le {n : ℕ} (b : Module.Basis (Fin n) ℝ F)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞)) :
    unconditionalBasisConstant
      (b.map (selectedHilbertEquiv F R S p D hp hdec hD).toLinearEquiv) ≤
        ((D * K : ℝ≥0) : ℝ≥0∞) := by
  have hK : (1 : ℝ≥0) ≤ K := by
    exact_mod_cast (one_le_unconditionalBasisConstant b).trans hb
  have hDK : (1 : ℝ≥0) ≤ D * K := one_le_mul hD hK
  have h := unconditionalBasisConstant_map_le b
    (selectedHilbertEquiv F R S p D hp hdec hD) 1 D K hb
    (fun y => by simpa only [NNReal.coe_one, one_mul] using
      selectedHilbertEquiv_contracts F R S p D hp hdec hD y)
    (selectedHilbertEquiv_symm_bound F R S p D hp hdec hD)
  simpa only [one_mul, mul_comm K D, max_eq_right (by exact_mod_cast hDK :
    (1 : ℝ≥0∞) ≤ ((D * K : ℝ≥0) : ℝ≥0∞))] using h

/-- The first coordinate on the selected image, in the original norm of E. -/
def selectedHilbertFirstProjection : (selectedHilbertMap F R S p D hp).range →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E p.Space).comp (selectedHilbertMap F R S p D hp).range.subtypeL

omit hdec hD in
theorem norm_selectedHilbertFirstProjection_le_one :
    ‖selectedHilbertFirstProjection F R S p D hp‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  change ‖(y : WithLp 2 (E × p.Space)).fst‖ ≤ 1 * ‖y‖
  simpa only [one_mul, Submodule.norm_coe] using WithLp.norm_fst_le (p := 2) (β := p.Space) E
    (y : WithLp 2 (E × p.Space))

/-- Lift the selected coordinate map into the new image. -/
def selectedHilbertLift (Q : Y →L[ℝ] F) (I : E →L[ℝ] Y) :
    E →L[ℝ] (selectedHilbertMap F R S p D hp).range :=
  (selectedHilbertEquiv F R S p D hp hdec hD).toContinuousLinearMap.comp (Q.comp I)

theorem norm_selectedHilbertLift_le (Q : Y →L[ℝ] F) (I : E →L[ℝ] Y)
    (K : ℝ≥0) (hQ : ‖Q‖ ≤ K) (hI : ‖I‖ ≤ 1) :
    ‖selectedHilbertLift F R S p D hp hdec hD Q I‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ K.2
  intro x
  have hIx : ‖I x‖ ≤ ‖x‖ :=
    (I.le_opNorm x).trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hI (norm_nonneg x))
  calc
    ‖selectedHilbertLift F R S p D hp hdec hD Q I x‖ ≤ ‖Q (I x)‖ :=
      selectedHilbertEquiv_contracts F R S p D hp hdec hD _
    _ ≤ ‖Q‖ * ‖I x‖ := Q.le_opNorm _
    _ ≤ (K : ℝ) * ‖x‖ := mul_le_mul hQ hIx (norm_nonneg _) K.2

/-- The compressed endomorphism is unchanged, so its finite-dimensional trace is unchanged. -/
theorem selectedHilbertFirstProjection_lift (Q : Y →L[ℝ] F) (I : E →L[ℝ] Y) :
    (selectedHilbertFirstProjection F R S p D hp).comp
      (selectedHilbertLift F R S p D hp hdec hD Q I) =
        R.comp (F.subtypeL.comp (Q.comp I)) := by
  ext x
  change (selectedHilbertEquiv F R S p D hp hdec hD (Q (I x)) :
    WithLp 2 (E × p.Space)).fst = R (Q (I x))
  rw [selectedHilbertEquiv_coe, selectedHilbertMap_fst]

end Model

/-- The existence interface used by finite selection. All image norms are inherited,
and the first component remains the original Banach space E. -/
theorem exists_selectedHilbertReplacement
    (F : Submodule ℝ Y) [FiniteDimensional ℝ F]
    (R : Y →L[ℝ] E) (S : Y →L[ℝ] W)
    (hdec : ∀ y : Y, ‖y‖ ^ 2 = ‖R y‖ ^ 2 + ‖S y‖ ^ 2)
    (D : ℝ≥0) (hD : 1 ≤ D) (hlocal : HasHilbertNormWithin (F.map S.toLinearMap) D) :
    ∃ p : HilbertNormModel (F.map S.toLinearMap),
      ∃ U : F →L[ℝ] WithLp 2 (E × p.Space), ∃ e : F ≃L[ℝ] U.range,
        (∀ y : F, (e y : WithLp 2 (E × p.Space)) = U y) ∧
        (∀ y : F, (U y).fst = R y) ∧
        (∀ y : F, ‖U y‖ ≤ ‖y‖) ∧
        (∀ y : U.range, ‖e.symm y‖ ≤ (D : ℝ) * ‖y‖) ∧
        Module.finrank ℝ U.range = Module.finrank ℝ F ∧
        ∀ (n : ℕ) (b : Module.Basis (Fin n) ℝ F) (K : ℝ≥0),
          unconditionalBasisConstant b ≤ (K : ℝ≥0∞) →
          unconditionalBasisConstant (b.map e.toLinearEquiv) ≤ ((D * K : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨p, hp⟩ := hlocal.exists_model
  exact ⟨p, selectedHilbertMap F R S p D hp,
    selectedHilbertEquiv F R S p D hp hdec hD,
    selectedHilbertEquiv_coe F R S p D hp hdec hD,
    selectedHilbertMap_fst F R S p D hp,
    selectedHilbertMap_contracts F R S p D hp hdec,
    selectedHilbertEquiv_symm_bound F R S p D hp hdec hD,
    selectedHilbertRange_finrank F R S p D hp hdec hD,
    fun _ b K hb => selectedHilbertBasis_constant_le F R S p D hp hdec hD b K hb⟩

end ComplementedSubspace
