import ComplementedSubspace.FiniteCoordinateSelection
import ComplementedSubspace.SelectedHilbertReplacement

/-! Finite coordinate selection followed by an actual Hilbert replacement of
the selected tail. The first summand retains the frame space's Banach norm. -/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace ComplementedSubspace

variable (E W : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The concrete output consumed by the finite small-dimension obstruction. -/
def HasSelectedHilbertFactorization (D K : ℝ≥0) : Prop :=
  ∃ V : Submodule ℝ W, ∃ _ : FiniteDimensional ℝ V, ∃ p : HilbertNormModel V,
    ∃ F : Submodule ℝ (WithLp 2 (E × p.Space)), ∃ r : ℕ,
      ∃ b : Module.Basis (Fin r) ℝ F,
        r ≤ 3 * Module.finrank ℝ E ∧
        unconditionalBasisConstant b ≤ ((D * K : ℝ≥0) : ℝ≥0∞) ∧
        ∃ A : E →L[ℝ] F, ∃ B : F →L[ℝ] E,
          ‖A‖ ≤ (K : ℝ) ∧ ‖B‖ ≤ 1 ∧
          (∀ z : F, B z = (z : WithLp 2 (E × p.Space)).fst) ∧
          (Module.finrank ℝ E : ℝ) / 2 ≤ LinearMap.trace ℝ E (B.comp A).toLinearMap

variable {E W} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem selected_coordinates_have_hilbert_factorization {m : ℕ}
    (b : Module.Basis (Fin m) ℝ Y) (s : Finset (Fin m))
    (I : E →L[ℝ] Y) (R : Y →L[ℝ] E) (S : Y →L[ℝ] W)
    (hdec : ∀ y : Y, ‖y‖ ^ 2 = ‖R y‖ ^ 2 + ‖S y‖ ^ 2)
    (hI : ∀ x, ‖I x‖ ≤ ‖x‖)
    (D K : ℝ≥0) (hD : 1 ≤ D)
    (hcard : s.card ≤ 3 * Module.finrank ℝ E)
    (hQ : ‖basisSubsetProjection b s‖ ≤ (K : ℝ))
    (htrace : (Module.finrank ℝ E : ℝ) / 2 ≤
      LinearMap.trace ℝ E (R.comp ((basisSubsetProjection b s).comp I)).toLinearMap)
    (c : Module.Basis (Fin s.card) ℝ (basisSubsetProjection b s).range)
    (hc : unconditionalBasisConstant c ≤ (K : ℝ≥0∞))
    (hlocal : ∀ (V : Submodule ℝ W) [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ 3 * Module.finrank ℝ E → HasHilbertNormWithin V D) :
    HasSelectedHilbertFactorization E W D K := by
  let Q := basisSubsetProjection b s
  let F : Submodule ℝ Y := Q.range
  letI : FiniteDimensional ℝ F := Module.Finite.of_basis c
  let V : Submodule ℝ W := F.map S.toLinearMap
  have hVdim : Module.finrank ℝ V ≤ 3 * Module.finrank ℝ E := by
    apply (selectedTail_finrank_le F S).trans
    change Module.finrank ℝ (basisSubsetProjection b s).range ≤ 3 * Module.finrank ℝ E
    simpa only [Module.finrank_eq_card_basis c, Fintype.card_fin] using hcard
  obtain ⟨p, hp⟩ := (hlocal V hVdim).exists_model
  let U := selectedHilbertMap F R S p D hp
  let e := selectedHilbertEquiv F R S p D hp hdec hD
  let A := selectedHilbertLift F R S p D hp hdec hD Q.rangeRestrict I
  let B := selectedHilbertFirstProjection F R S p D hp
  have hQR : ‖Q.rangeRestrict‖ ≤ (K : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ K.2
    intro y
    exact (Q.le_opNorm y).trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg y))
  have hIop : ‖I‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using hI x
  have hBA : B.comp A = R.comp (Q.comp I) := by
    dsimp [A, B]
    rw [selectedHilbertFirstProjection_lift]
    rfl
  refine ⟨V, inferInstance, p, U.range, s.card, c.map e.toLinearEquiv, hcard,
    selectedHilbertBasis_constant_le F R S p D hp hdec hD c K hc, A, B,
    norm_selectedHilbertLift_le F R S p D hp hdec hD Q.rangeRestrict I K hQR hIop,
    norm_selectedHilbertFirstProjection_le_one F R S p D hp, (fun _ => rfl), ?_⟩
  rw [hBA]
  exact htrace

/-- Frame specialization with no assumed trace estimate. The local Hilbert
dimension threshold is three times the coefficient dimension. -/
theorem exists_frame_selectedHilbertFactorization {m n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    (b : Module.Basis (Fin m) ℝ Y)
    (I : FrameCoefficient n p →L[ℝ] Y) (R : Y →L[ℝ] FrameCoefficient n p)
    (J : W →L[ℝ] Y) (S : Y →L[ℝ] W)
    (hRI : R.comp I = ContinuousLinearMap.id ℝ (FrameCoefficient n p))
    (hJS : J.comp S = ContinuousLinearMap.id ℝ Y - I.comp R)
    (hdec : ∀ y : Y, ‖y‖ ^ 2 = ‖R y‖ ^ 2 + ‖S y‖ ^ 2)
    (hI : ∀ x, ‖I x‖ ≤ ‖x‖) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (D K : ℝ≥0) (hD : 1 ≤ D) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    (hlocal : ∀ (V : Submodule ℝ W) [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ 3 * Module.finrank ℝ (FrameCoefficient n p) →
      HasHilbertNormWithin V D)
    (hsmall : (((2 : ℝ) ^ n * realFrameSignConstant p / realFrameWitnessScale n p) *
      (D : ℝ) * (K : ℝ) ^ 2) ≤ (Module.finrank ℝ (FrameCoefficient n p) : ℝ) / 4) :
    HasSelectedHilbertFactorization (FrameCoefficient n p) W D K := by
  obtain ⟨s, hcard, hQ, htrace, c, hc⟩ := exists_frame_coordinate_selection hp₂ hp₄ b I R J S
    hRI hJS hI hR hJ hS K hb D.2
    (fun V _ hV => hlocal V (hV.trans (by omega))) hsmall
  exact selected_coordinates_have_hilbert_factorization b s I R S hdec hI D K hD
    hcard hQ htrace c hc hlocal

end ComplementedSubspace
