import ComplementedSubspace.DPRtoGL

/-! # A subfamily of a finite unconditional basis retains its constant -/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem unconditionalBasisConstant_restriction_le {m n : ℕ}
    (b : Module.Basis (Fin m) ℝ E) {F : Submodule ℝ E}
    (c : Module.Basis (Fin n) ℝ F) (e : Fin n → Fin m)
    (he : Function.Injective e) (hc : ∀ i, (c i : E) = b (e i))
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞)) :
    unconditionalBasisConstant c ≤ (K : ℝ≥0∞) := by
  classical
  apply max_le ((one_le_unconditionalBasisConstant b).trans hb)
  refine iSup_le fun θ => iSup_le fun hθ => ?_
  let θ' : Fin m → ℝ := Function.extend e θ (fun _ => 0)
  have hθ' (j : Fin m) : ‖θ' j‖ ≤ 1 := by
    dsimp [θ']
    rw [Function.extend_def]
    split_ifs
    · exact hθ _
    · simp
  have hext (i : Fin n) : θ' (e i) = θ i := he.extend_apply θ (fun _ => 0) i
  have hcomp : F.subtypeL.comp (basisMultiplier c θ) =
      (basisMultiplier b θ').comp F.subtypeL := by
    apply ContinuousLinearMap.coe_injective
    apply c.ext
    intro i
    change (basisMultiplier c θ (c i) : E) = basisMultiplier b θ' (c i : E)
    rw [basisMultiplier_apply_basis, Submodule.coe_smul, hc,
      basisMultiplier_apply_basis, hext]
  apply enorm_le_coe.mpr
  apply NNReal.coe_le_coe.mp
  apply ContinuousLinearMap.opNorm_le_bound _ K.2
  intro z
  have heq := congrArg (fun T : F →L[ℝ] E => T z) hcomp
  change ‖(basisMultiplier c θ z : E)‖ ≤ (K : ℝ) * ‖z‖
  change (basisMultiplier c θ z : E) = basisMultiplier b θ' (z : E) at heq
  rw [heq]
  exact norm_basisMultiplier_le_bound b K hb ⟨θ', hθ'⟩ (z : E)

/-- An injectively indexed subfamily gives a basis of its exact span in the
original ambient norm, without any loss of unconditional constant. -/
theorem exists_unconditional_basis_of_subfamily {m n : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (e : Fin n → Fin m) (he : Function.Injective e)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞)) :
    ∃ c : Module.Basis (Fin n) ℝ (Submodule.span ℝ (Set.range (fun i => b (e i)))),
      (∀ i, (c i : E) = b (e i)) ∧ unconditionalBasisConstant c ≤ (K : ℝ≥0∞) := by
  let hli := b.linearIndependent.comp e he
  let c := Module.Basis.span hli
  refine ⟨c, fun i => Module.Basis.coe_span_apply hli i, ?_⟩
  exact unconditionalBasisConstant_restriction_le b c e he
    (fun i => Module.Basis.coe_span_apply hli i) K hb

end ComplementedSubspace
