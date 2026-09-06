import ComplementedSubspace.FiniteBasisTraceBound
import ComplementedSubspace.BasisRestriction

/-! # Selected finite coordinate ranges, with inherited unconditional norm -/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace ComplementedSubspace

variable {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def basisSubsetProjection {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (s : Finset (Fin m)) : Y →L[ℝ] Y :=
  basisMultiplier b (fun i => if i ∈ s then 1 else 0)

theorem basisSubsetProjection_apply {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (s : Finset (Fin m)) (y : Y) :
    basisSubsetProjection b s y = ∑ i ∈ s, b.coord i y • b i := by
  classical
  change b.constr ℝ (fun i => (if i ∈ s then (1 : ℝ) else 0) • b i) y = _
  rw [Module.Basis.constr_apply_fintype]
  simp [Module.Basis.coord_apply, Module.Basis.equivFun_apply]

theorem basisSubsetProjection_norm_le {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (s : Finset (Fin m)) (K : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞)) :
    ‖basisSubsetProjection b s‖ ≤ (K : ℝ) := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ K.2
  intro y
  exact norm_basisMultiplier_le_bound b K hb
    ⟨fun i => if i ∈ s then 1 else 0, by intro i; dsimp; split_ifs <;> norm_num⟩ y

theorem basisSubsetProjection_range {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (s : Finset (Fin m)) :
    (basisSubsetProjection b s).range = Submodule.span ℝ (b '' (s : Set (Fin m))) := by
  classical
  apply le_antisymm
  · rintro y ⟨z, rfl⟩
    change basisSubsetProjection b s z ∈ Submodule.span ℝ (b '' (s : Set (Fin m)))
    rw [basisSubsetProjection_apply]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro y ⟨i, hi, rfl⟩
    change i ∈ s at hi
    refine ⟨b i, ?_⟩
    simp [basisSubsetProjection, basisMultiplier_apply_basis, hi]

theorem basisSubsetProjection_exists_basis {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (s : Finset (Fin m)) (K : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞)) :
    ∃ c : Module.Basis (Fin s.card) ℝ (basisSubsetProjection b s).range,
      unconditionalBasisConstant c ≤ (K : ℝ≥0∞) := by
  classical
  let e : Fin s.card ≃ s := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin s).symm
  let f : Fin s.card → Fin m := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hli := b.linearIndependent.comp f hf
  have hspan : Submodule.span ℝ (Set.range (fun i => b (f i))) =
      (basisSubsetProjection b s).range := by
    rw [basisSubsetProjection_range]
    congr 1
    apply Set.ext
    intro y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨f i, (e i).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e.symm ⟨i, hi⟩, by simp [f]⟩
  let c := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  refine ⟨c, unconditionalBasisConstant_restriction_le b c f hf ?_ K hb⟩
  intro i
  simp only [c, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply, Function.comp_apply]

theorem basisSubsetProjection_compressed_trace {m : ℕ}
    (b : Module.Basis (Fin m) ℝ Y) (s : Finset (Fin m))
    (I : E →L[ℝ] Y) (R : Y →L[ℝ] E) :
    LinearMap.trace ℝ E (R.comp ((basisSubsetProjection b s).comp I)).toLinearMap =
      ∑ i ∈ s, LinearMap.trace ℝ E (compressedBasisMap b I.toLinearMap R.toLinearMap i) := by
  have heq : (R.comp ((basisSubsetProjection b s).comp I)).toLinearMap =
      ∑ i ∈ s, compressedBasisMap b I.toLinearMap R.toLinearMap i := by
    ext x
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      basisSubsetProjection_apply, map_sum, map_smul, LinearMap.sum_apply,
      compressedBasisMap, basisCoordinateMap, LinearMap.comp_apply,
      LinearMap.smulRight_apply]
  rw [heq, map_sum]

end ComplementedSubspace
