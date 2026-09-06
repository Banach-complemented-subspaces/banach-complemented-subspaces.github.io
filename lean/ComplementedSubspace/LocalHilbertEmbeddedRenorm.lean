import ComplementedSubspace.LocalHilbertQuotient

/-! Restrict a global renorming to an actual isometrically embedded subspace.
The resulting equivalence preserves the global distortion bounds and gives
the dual-subspace geometry without requiring the embedding to be onto. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

universe u v w

variable {W : Type w} {E : Type u} {F : Type v}
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev embeddedRenormSpace (i : W →ₗᵢ[ℝ] E) (e : E ≃L[ℝ] F) :=
  i.toLinearMap.range.map e.toLinearMap

def embeddedRenormEquiv (i : W →ₗᵢ[ℝ] E) (e : E ≃L[ℝ] F) :
    W ≃L[ℝ] embeddedRenormSpace i e :=
  i.equivRange.toContinuousLinearEquiv.trans (e.submoduleMap i.toLinearMap.range)

@[simp] theorem embeddedRenormEquiv_apply_coe
    (i : W →ₗᵢ[ℝ] E) (e : E ≃L[ℝ] F) (x : W) :
    (embeddedRenormEquiv i e x : F) = e (i x) := rfl

theorem embeddedRenormEquiv_norm_le (i : W →ₗᵢ[ℝ] E) (e : E ≃L[ℝ] F)
    {D : ℝ} (hD : 0 ≤ D) (he : ‖e.toContinuousLinearMap‖ ≤ D) :
    ‖(embeddedRenormEquiv i e).toContinuousLinearMap‖ ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro x
  change ‖e (i x)‖ ≤ D * ‖x‖
  calc
    ‖e (i x)‖ ≤ ‖e.toContinuousLinearMap‖ * ‖i x‖ :=
      e.toContinuousLinearMap.le_opNorm _
    _ ≤ D * ‖i x‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ = D * ‖x‖ := by rw [i.norm_map]

theorem embeddedRenormEquiv_symm_norm_le (i : W →ₗᵢ[ℝ] E) (e : E ≃L[ℝ] F)
    {D : ℝ} (hD : 0 ≤ D) (he : ‖e.symm.toContinuousLinearMap‖ ≤ D) :
    ‖(embeddedRenormEquiv i e).symm.toContinuousLinearMap‖ ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro x
  change ‖i.equivRange.symm ((e.submoduleMap i.toLinearMap.range).symm x)‖ ≤ D * ‖x‖
  rw [i.equivRange.symm.norm_map]
  exact ((e.submoduleMap i.toLinearMap.range).symm.toContinuousLinearMap.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (submoduleMap_symm_norm_le e _ hD he) (norm_nonneg x))

theorem embeddedRenormSpace_approxParallelogram
    (i : W →ₗᵢ[ℝ] E) (e : E ≃L[ℝ] F) {ν : ℝ}
    (hpar : ApproxParallelogram (fun x : F => ‖x‖) ν) :
    ApproxParallelogram (fun x : embeddedRenormSpace i e => ‖x‖) ν :=
  hpar.subspace (embeddedRenormSpace i e)

/-- An ambient renorming also controls duals of arbitrary dual subspaces of
any isometrically embedded space, with the same distortion product. -/
theorem embedded_renorm_dual_subspace_dual_localHilbert {D ν η : ℝ} {d : ℕ}
    (hD : 0 ≤ D)
    (hgood : ∀ (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G],
      ApproxParallelogram (fun x : G => ‖x‖) ν → LocallyHilbertWithin G d η)
    (i : W →ₗᵢ[ℝ] E) (e : E ≃L[ℝ] F)
    (he : ‖e.toContinuousLinearMap‖ ≤ 1)
    (hei : ‖e.symm.toContinuousLinearMap‖ ≤ D)
    (hpar : ApproxParallelogram (fun x : F => ‖x‖) ν) :
    DualSubspacesLocallyHilbertWithin (StrongDual ℝ W) d (D * η) := by
  exact renorm_dual_subspace_dual_localHilbert hD hgood (embeddedRenormEquiv i e)
    (embeddedRenormEquiv_norm_le i e zero_le_one he)
    (embeddedRenormEquiv_symm_norm_le i e hD hei)
    (embeddedRenormSpace_approxParallelogram i e hpar)

end ComplementedSubspace
