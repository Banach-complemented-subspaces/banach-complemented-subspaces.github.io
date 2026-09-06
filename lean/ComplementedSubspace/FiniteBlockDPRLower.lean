import ComplementedSubspace.FiniteBlockObstruction
import ComplementedSubspace.FiniteSuperspaceSplitting
import ComplementedSubspace.LocalHilbertTransport
import ComplementedSubspace.DPRObstruction

/-! # A distinguished frame block forces a lower bound on chiDPR -/

noncomputable section
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem frame_block_le_chiDPR {n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (I : FrameCoefficient n p →L[ℝ] Z) (R : Z →L[ℝ] FrameCoefficient n p)
    (J : W →L[ℝ] Z) (S : Z →L[ℝ] W)
    (hRI : R.comp I = ContinuousLinearMap.id ℝ (FrameCoefficient n p))
    (hJS : J.comp S = ContinuousLinearMap.id ℝ Z - I.comp R)
    (hdec : ∀ z : Z, ‖z‖ ^ 2 = ‖R z‖ ^ 2 + ‖S z‖ ^ 2)
    (hI : ∀ x, ‖I x‖ ≤ ‖x‖) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (D K : ℝ≥0) (hD : 2 ≤ D) (hK : 1 ≤ K)
    (hlocal : ∀ (V : Submodule ℝ W) [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ 3 * 2 ^ n → HasHilbertNormWithin V D)
    (hDK : 8 * K ≤ D) (hL : (D : ℝ) ^ 8 < realFrameOverlapScale n p) :
    (K : ℝ≥0∞) ≤ chiDPR Z := by
  letI : Nontrivial (FrameCoefficient n p) :=
    Module.nontrivial_of_finrank_pos (by rw [frameCoefficient_finrank]; positivity)
  have hV : I.range ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : FrameCoefficient n p)
    have hIx : I x = 0 := by
      have hmem : I x ∈ I.range := ⟨x, rfl⟩
      simpa only [hbot, Submodule.mem_bot] using hmem
    have h := congrArg (fun T : FrameCoefficient n p →L[ℝ] FrameCoefficient n p => T x) hRI
    have hx0 : x = 0 := by simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, hIx, map_zero] using h.symm
    exact hx hx0
  apply le_chiDPR_of_basis_obstruction K I.range inferInstance hV
  intro F hIF _ m b
  apply le_of_lt
  apply lt_of_not_ge
  intro hb
  apply finite_basis_obstruction_with_frame_summand_of_scale hp₂ hp₃ b
    (SuperspaceSplitting.inclusion F I hIF) (SuperspaceSplitting.first F R)
    (SuperspaceSplitting.tailInclusion F I R J S hIF hJS) (SuperspaceSplitting.second F S)
    (SuperspaceSplitting.first_inclusion F I R hIF hRI)
    (SuperspaceSplitting.tail_second F I R J S hIF hJS)
    (SuperspaceSplitting.norm_sq_decomposition F R S hdec)
    (SuperspaceSplitting.inclusion_contracts F I hIF hI)
    (SuperspaceSplitting.first_contracts F R hR)
    (SuperspaceSplitting.tailInclusion_contracts F I R J S hIF hJS hJ)
    (SuperspaceSplitting.second_contracts F S hS)
    D K hD hK hb _ hDK hL
  intro V _ hVdim
  exact localHilbert_subspace hlocal (F.map S.toLinearMap) V hVdim

end ComplementedSubspace
