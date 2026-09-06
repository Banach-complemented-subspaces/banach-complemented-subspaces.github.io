import ComplementedSubspace.FiniteSelectedHilbertModel
import ComplementedSubspace.FiniteOverlapObstruction

/-! # The finite basis obstruction in a space with a distinguished frame summand -/

noncomputable section
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

theorem frameCoefficient_finrank (n : ℕ) (p : ℝ) :
    Module.finrank ℝ (FrameCoefficient n p) = 2 ^ n := by
  change Module.finrank ℝ (MomentIndex n → ℝ) = _
  rw [Module.finrank_fintype_fun_eq_card, momentIndex_card]

variable {Y W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem finite_basis_obstruction_with_frame_summand {m n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (b : Module.Basis (Fin m) ℝ Y)
    (I : FrameCoefficient n p →L[ℝ] Y) (R : Y →L[ℝ] FrameCoefficient n p)
    (J : W →L[ℝ] Y) (S : Y →L[ℝ] W)
    (hRI : R.comp I = ContinuousLinearMap.id ℝ (FrameCoefficient n p))
    (hJS : J.comp S = ContinuousLinearMap.id ℝ Y - I.comp R)
    (hdec : ∀ y : Y, ‖y‖ ^ 2 = ‖R y‖ ^ 2 + ‖S y‖ ^ 2)
    (hI : ∀ x, ‖I x‖ ≤ ‖x‖) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (D K : ℝ≥0) (hD : 1 ≤ D) (hK : 1 ≤ K)
    (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    (hlocal : ∀ (V : Submodule ℝ W) [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ 3 * 2 ^ n → HasHilbertNormWithin V D)
    (hsmall : (((2 : ℝ) ^ n * realFrameSignConstant p / realFrameWitnessScale n p) *
      (D : ℝ) * (K : ℝ) ^ 2) ≤ (2 : ℝ) ^ n / 4)
    (hsep : 256 * (K : ℝ) ^ 2 * realFrameSignConstant p ^ 2 * ((D : ℝ) * (K : ℝ)) ^ 3 <
      realFrameOverlapScale n p) : False := by
  have hlocal' : ∀ (V : Submodule ℝ W) [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ 3 * Module.finrank ℝ (FrameCoefficient n p) →
      HasHilbertNormWithin V D := by
    simpa only [frameCoefficient_finrank] using hlocal
  have hsmall' : (((2 : ℝ) ^ n * realFrameSignConstant p / realFrameWitnessScale n p) *
      (D : ℝ) * (K : ℝ) ^ 2) ≤ (Module.finrank ℝ (FrameCoefficient n p) : ℝ) / 4 := by
    simpa only [frameCoefficient_finrank, Nat.cast_pow, Nat.cast_ofNat] using hsmall
  obtain ⟨V, hV, model, F, r, c, hr, hc, A, B, hA, _, hfirst, htrace⟩ :=
    exists_frame_selectedHilbertFactorization hp₂ (by linarith) b I R J S hRI hJS hdec
      hI hR hJ hS D K hD hb hlocal' hsmall'
  letI : FiniteDimensional ℝ F := Module.Finite.of_basis c
  have hB : B = selectedProductFst F := by
    ext z
    exact hfirst z
  have hr' : (r : ℝ) ≤ 3 * (2 : ℝ) ^ n := by
    rw [frameCoefficient_finrank] at hr
    exact_mod_cast hr
  have htrace' : (2 : ℝ) ^ n / 2 ≤ LinearMap.trace ℝ (FrameCoefficient n p)
      ((selectedProductFst F).comp A).toLinearMap := by
    simpa only [hB, frameCoefficient_finrank, Nat.cast_pow, Nat.cast_ofNat] using htrace
  have hC : (1 : ℝ) ≤ ((D * K : ℝ≥0) : ℝ) := by
    exact_mod_cast (one_le_mul_of_one_le_of_one_le hD hK)
  have hsep' : 256 * (K : ℝ) ^ 2 * realFrameSignConstant p ^ 2 *
      ((D * K : ℝ≥0) : ℝ) ^ 3 < realFrameOverlapScale n p := by
    change 256 * (K : ℝ) ^ 2 * realFrameSignConstant p ^ 2 *
      ((D : ℝ) * (K : ℝ)) ^ 3 < realFrameOverlapScale n p
    exact hsep
  exact finite_selected_trace_obstruction (H := model.Space) n p hp₂ hp₃ F c (D * K)
    hC hc hr' A (K := (K : ℝ)) K.2 hA htrace' hsep'

theorem finite_basis_obstruction_with_frame_summand_of_scale {m n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (b : Module.Basis (Fin m) ℝ Y)
    (I : FrameCoefficient n p →L[ℝ] Y) (R : Y →L[ℝ] FrameCoefficient n p)
    (J : W →L[ℝ] Y) (S : Y →L[ℝ] W)
    (hRI : R.comp I = ContinuousLinearMap.id ℝ (FrameCoefficient n p))
    (hJS : J.comp S = ContinuousLinearMap.id ℝ Y - I.comp R)
    (hdec : ∀ y : Y, ‖y‖ ^ 2 = ‖R y‖ ^ 2 + ‖S y‖ ^ 2)
    (hI : ∀ x, ‖I x‖ ≤ ‖x‖) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (D K : ℝ≥0) (hD : 2 ≤ D) (hK : 1 ≤ K)
    (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    (hlocal : ∀ (V : Submodule ℝ W) [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ 3 * 2 ^ n → HasHilbertNormWithin V D)
    (hDK : 8 * K ≤ D) (hL : (D : ℝ) ^ 8 < realFrameOverlapScale n p) : False := by
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hDKr : 8 * (K : ℝ) ≤ D := by exact_mod_cast hDK
  obtain ⟨hsmall, hsep⟩ := finite_frame_selection_scalar_bounds n p D K
    hp₂ hp₃ hDr K.2 hDKr hL
  exact finite_basis_obstruction_with_frame_summand hp₂ hp₃ b I R J S hRI hJS hdec
    hI hR hJ hS D K ((by norm_num : (1 : ℝ≥0) ≤ 2).trans hD) hK hb hlocal hsmall hsep

end ComplementedSubspace
