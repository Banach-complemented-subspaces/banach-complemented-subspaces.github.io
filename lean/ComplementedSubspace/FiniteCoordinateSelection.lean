import ComplementedSubspace.FiniteSelectionCoordinates
import ComplementedSubspace.FiniteTraceSelection
import ComplementedSubspace.ProductFrameTraceBound

/-! # Actual finite coordinate selection from a small trace defect

The selected range carries an actual restricted basis, with its inherited
norm and the original unconditional bound. The frame specialization uses
the proved Hilbert-factorization estimate for the constructed frame norm.
-/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace ComplementedSubspace

variable {Y E W : Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_basis_coordinate_selection {m : ℕ}
    (b : Module.Basis (Fin m) ℝ Y) (I : E →L[ℝ] Y) (R : Y →L[ℝ] E)
    (hRI : R.comp I = ContinuousLinearMap.id ℝ E)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    (hdefect : (∑ i, |LinearMap.trace ℝ E
        (compressedBasisMap b I.toLinearMap R.toLinearMap i) -
      (LinearMap.trace ℝ E (compressedBasisMap b I.toLinearMap R.toLinearMap i)) ^ 2|) ≤
        (Module.finrank ℝ E : ℝ) / 4) :
    ∃ s : Finset (Fin m), s.card ≤ 3 * Module.finrank ℝ E ∧
      ‖basisSubsetProjection b s‖ ≤ (K : ℝ) ∧
      (Module.finrank ℝ E : ℝ) / 2 ≤
        LinearMap.trace ℝ E (R.comp ((basisSubsetProjection b s).comp I)).toLinearMap ∧
      ∃ c : Module.Basis (Fin s.card) ℝ (basisSubsetProjection b s).range,
        unconditionalBasisConstant c ≤ (K : ℝ≥0∞) := by
  have hRI' : R.toLinearMap.comp I.toLinearMap = LinearMap.id :=
    congrArg ContinuousLinearMap.toLinearMap hRI
  obtain ⟨s, hcard, hlo, _, _⟩ := exists_finite_trace_selection
    (fun i => LinearMap.trace ℝ E (compressedBasisMap b I.toLinearMap R.toLinearMap i))
    (q := (Module.finrank ℝ E : ℝ)) (η := (1 / 8 : ℝ)) (by positivity) (by norm_num)
    (sum_compressedBasisMap_trace b I.toLinearMap R.toLinearMap hRI')
    (by convert hdefect using 1 <;> ring)
  refine ⟨s, ?_, basisSubsetProjection_norm_le b s K hb, ?_,
    basisSubsetProjection_exists_basis b s K hb⟩
  · exact_mod_cast hcard
  · rw [basisSubsetProjection_compressed_trace]
    convert hlo using 1 <;> ring

/-- Selection for the actual frame space. No trace inequality is left as an
assumption: the only analytic input is local Hilbert approximation of W. -/
theorem exists_frame_coordinate_selection {m n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    (b : Module.Basis (Fin m) ℝ Y)
    (I : FrameCoefficient n p →L[ℝ] Y) (R : Y →L[ℝ] FrameCoefficient n p)
    (J : W →L[ℝ] Y) (S : Y →L[ℝ] W)
    (hRI : R.comp I = ContinuousLinearMap.id ℝ (FrameCoefficient n p))
    (hJS : J.comp S = ContinuousLinearMap.id ℝ Y - I.comp R)
    (hI : ∀ x, ‖I x‖ ≤ ‖x‖) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlocal : ∀ (F : Submodule ℝ W) [FiniteDimensional ℝ F],
      Module.finrank ℝ F ≤ Module.finrank ℝ (FrameCoefficient n p) →
      HasHilbertNormWithin F D)
    (hsmall : (((2 : ℝ) ^ n * realFrameSignConstant p / realFrameWitnessScale n p) *
      D * (K : ℝ) ^ 2) ≤ (Module.finrank ℝ (FrameCoefficient n p) : ℝ) / 4) :
    ∃ s : Finset (Fin m), s.card ≤ 3 * Module.finrank ℝ (FrameCoefficient n p) ∧
      ‖basisSubsetProjection b s‖ ≤ (K : ℝ) ∧
      (Module.finrank ℝ (FrameCoefficient n p) : ℝ) / 2 ≤
        LinearMap.trace ℝ (FrameCoefficient n p)
          (R.comp ((basisSubsetProjection b s).comp I)).toLinearMap ∧
      ∃ c : Module.Basis (Fin s.card) ℝ (basisSubsetProjection b s).range,
        unconditionalBasisConstant c ≤ (K : ℝ≥0∞) := by
  apply exists_basis_coordinate_selection b I R hRI K hb
  apply le_trans (finite_basis_trace_defect_le b I R J S hJS hI hR hJ hS K hb
    hD (by exact div_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg (by norm_num) _)) (Real.exp_pos _).le)
    (le_refl _) hlocal ?_) hsmall
  intro F _ model U V
  exact realFrame_hilbert_trace_bound n p hp₂ hp₄ U V

end ComplementedSubspace
