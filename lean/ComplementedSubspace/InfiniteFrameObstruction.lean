import ComplementedSubspace.FiniteBlockDPRLower

/-! # Infinite DPR from an unbounded family of actual frame summands -/

noncomputable section
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {ι Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem chiDPR_eq_top_of_frame_summands
    (n : ι → ℕ) (p : ι → ℝ) [∀ i, Fact (1 ≤ ENNReal.ofReal (p i))]
    (hp₂ : ∀ i, 2 ≤ p i) (hp₃ : ∀ i, p i ≤ 3)
    (W : ι → Type*) [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (I : ∀ i, FrameCoefficient (n i) (p i) →L[ℝ] Z)
    (R : ∀ i, Z →L[ℝ] FrameCoefficient (n i) (p i))
    (J : ∀ i, W i →L[ℝ] Z) (S : ∀ i, Z →L[ℝ] W i)
    (hRI : ∀ i, (R i).comp (I i) = ContinuousLinearMap.id ℝ (FrameCoefficient (n i) (p i)))
    (hJS : ∀ i, (J i).comp (S i) = ContinuousLinearMap.id ℝ Z - (I i).comp (R i))
    (hdec : ∀ i (z : Z), ‖z‖ ^ 2 = ‖R i z‖ ^ 2 + ‖S i z‖ ^ 2)
    (hI : ∀ i x, ‖I i x‖ ≤ ‖x‖) (hR : ∀ i x, ‖R i x‖ ≤ ‖x‖)
    (hJ : ∀ i x, ‖J i x‖ ≤ ‖x‖) (hS : ∀ i x, ‖S i x‖ ≤ ‖x‖)
    (D : ι → ℝ≥0) (hD : ∀ i, 2 ≤ D i)
    (hlocal : ∀ i (V : Submodule ℝ (W i)) [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ 3 * 2 ^ n i → HasHilbertNormWithin V (D i))
    (hL : ∀ i, (D i : ℝ) ^ 8 < realFrameOverlapScale (n i) (p i))
    (hlarge : ∀ K : ℝ≥0, ∃ i, 8 * max 1 K ≤ D i) : chiDPR Z = ⊤ := by
  apply chiDPR_eq_top_of_nnreal_lower_bounds
  intro K
  obtain ⟨i, hi⟩ := hlarge K
  have hbound := frame_block_le_chiDPR (hp₂ i) (hp₃ i) (I i) (R i) (J i) (S i)
    (hRI i) (hJS i) (hdec i) (hI i) (hR i) (hJ i) (hS i)
    (D i) (max 1 K) (hD i) (le_max_left _ _) (hlocal i) hi (hL i)
  exact (ENNReal.coe_le_coe.mpr (le_max_right (1 : ℝ≥0) K)).trans hbound

end ComplementedSubspace
