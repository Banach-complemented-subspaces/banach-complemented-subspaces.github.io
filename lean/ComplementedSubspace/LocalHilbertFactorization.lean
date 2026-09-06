import ComplementedSubspace.LocalHilbert

/-!
# Factorization through a locally Hilbertian range

A map from a finite-dimensional space into a locally Hilbertian space has a
Hilbertian range of no larger dimension. Renorm this range using the actual
Hilbert model already constructed by the local compactness argument. Composing
with a map out of the ambient space then gives a genuine Hilbert factorization,
with separate bounds on the two factors. This is the input required by the
finite selection trace-defect argument.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

namespace ComplementedSubspace

variable {E : Type u} {W : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem rangeRestrict_norm_eq (A : E →L[ℝ] W) : ‖A.rangeRestrict‖ = ‖A‖ := by
  apply le_antisymm
  · exact A.rangeRestrict.opNorm_le_bound (norm_nonneg A) fun x => A.le_opNorm x
  · exact A.opNorm_le_bound (norm_nonneg A.rangeRestrict) fun x =>
      A.rangeRestrict.le_opNorm x

/-- Renorming the range gives an actual Hilbert factorization, with the loss
placed in the second factor. The model has the same underlying vector space
as the range, so it is finite-dimensional whenever the original domain is. -/
theorem exists_hilbertFactorization_of_range {D : ℝ} (hD : 0 ≤ D)
    (A : E →L[ℝ] W) (B : W →L[ℝ] F)
    (h : HasHilbertNormWithin ↥A.range D) :
    ∃ p : HilbertNormModel ↥A.range,
      ∃ U : E →L[ℝ] p.Space, ∃ V : p.Space →L[ℝ] F,
        V.comp U = B.comp A ∧ ‖U‖ ≤ ‖A‖ ∧ ‖V‖ ≤ D * ‖B‖ := by
  obtain ⟨p, hp⟩ := h.exists_model
  let e := p.equivOfBounds D hp
  let U : E →L[ℝ] p.Space := e.toContinuousLinearMap.comp A.rangeRestrict
  let B' : ↥A.range →L[ℝ] F := B.comp A.range.subtypeL
  let V : p.Space →L[ℝ] F := B'.comp e.symm.toContinuousLinearMap
  have he : ‖e.toContinuousLinearMap‖ ≤ 1 := p.norm_equivOfBounds_le D hp
  have hei : ‖e.symm.toContinuousLinearMap‖ ≤ D := p.norm_equivOfBounds_symm_le hD hp
  have hB : ‖B'‖ ≤ ‖B‖ := by
    apply B'.opNorm_le_bound (norm_nonneg B)
    intro x
    exact B.le_opNorm x
  refine ⟨p, U, V, ?_, ?_, ?_⟩
  · ext x
    change B (e.symm (e (A.rangeRestrict x))) = B (A x)
    rw [e.symm_apply_apply]
    rfl
  · calc
      ‖U‖ ≤ ‖e.toContinuousLinearMap‖ * ‖A.rangeRestrict‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖A.rangeRestrict‖ :=
        mul_le_mul_of_nonneg_right he (norm_nonneg A.rangeRestrict)
      _ = ‖A‖ := by rw [one_mul, rangeRestrict_norm_eq]
  · calc
      ‖V‖ ≤ ‖B'‖ * ‖e.symm.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖B‖ * D := mul_le_mul hB hei (norm_nonneg _) (norm_nonneg _)
      _ = D * ‖B‖ := mul_comm _ _

/-- Local Hilbert approximation supplies the range hypothesis uniformly for
every map whose finite-dimensional domain has dimension at most `q`. -/
theorem exists_hilbertFactorization_of_local [FiniteDimensional ℝ E]
    {q : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (hlocal : ∀ (S : Submodule ℝ W) [FiniteDimensional ℝ S], Module.finrank ℝ S ≤ q →
      HasHilbertNormWithin S D)
    (hE : Module.finrank ℝ E ≤ q) (A : E →L[ℝ] W) (B : W →L[ℝ] F) :
    ∃ p : HilbertNormModel ↥A.range,
      ∃ U : E →L[ℝ] p.Space, ∃ V : p.Space →L[ℝ] F,
        V.comp U = B.comp A ∧ ‖U‖ ≤ ‖A‖ ∧ ‖V‖ ≤ D * ‖B‖ := by
  apply exists_hilbertFactorization_of_range hD A B
  apply hlocal A.range
  exact (LinearMap.finrank_range_le A.toLinearMap).trans hE

/-- Product form of the two factor bounds, for trace estimates. -/
theorem exists_hilbertFactorization_norm_product [FiniteDimensional ℝ E]
    {q : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (hlocal : ∀ (S : Submodule ℝ W) [FiniteDimensional ℝ S], Module.finrank ℝ S ≤ q →
      HasHilbertNormWithin S D)
    (hE : Module.finrank ℝ E ≤ q) (A : E →L[ℝ] W) (B : W →L[ℝ] F) :
    ∃ p : HilbertNormModel ↥A.range,
      ∃ U : E →L[ℝ] p.Space, ∃ V : p.Space →L[ℝ] F,
        V.comp U = B.comp A ∧ ‖U‖ * ‖V‖ ≤ D * ‖A‖ * ‖B‖ := by
  obtain ⟨p, U, V, hcomp, hU, hV⟩ :=
    exists_hilbertFactorization_of_local hD hlocal hE A B
  refine ⟨p, U, V, hcomp, ?_⟩
  calc
    ‖U‖ * ‖V‖ ≤ ‖A‖ * (D * ‖B‖) :=
      mul_le_mul hU hV (norm_nonneg _) (norm_nonneg _)
    _ = D * ‖A‖ * ‖B‖ := by ring

end ComplementedSubspace
