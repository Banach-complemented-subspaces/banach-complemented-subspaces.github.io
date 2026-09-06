import ComplementedSubspace.LocalHilbertSum
import ComplementedSubspace.LocalHilbertProperty

/-!
# Renorming before passing to a subspace dual

A global renorming with a small parallelogram constant is transported to an
arbitrary subspace of the dual. Only after restricting the norm do we take
another dual. This controls finite dimensional subspaces of its dual, the
quotient-type operation needed by the main dual obstruction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def dualRenormEquiv (e : E ≃L[ℝ] F) : StrongDual ℝ E ≃L[ℝ] StrongDual ℝ F :=
  e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem dualRenormEquiv_norm_le (e : E ≃L[ℝ] F) {D : ℝ} (hD : 0 ≤ D)
    (he : ‖e.symm.toContinuousLinearMap‖ ≤ D) :
    ‖(dualRenormEquiv e).toContinuousLinearMap‖ ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro φ
  change ‖dualRenormEquiv e φ‖ ≤ D * ‖φ‖
  have hid : dualRenormEquiv e φ = φ.comp e.symm.toContinuousLinearMap := by ext x; rfl
  rw [hid]
  calc
    _ ≤ ‖φ‖ * ‖e.symm.toContinuousLinearMap‖ := φ.opNorm_comp_le _
    _ ≤ ‖φ‖ * D := mul_le_mul_of_nonneg_left he (norm_nonneg φ)
    _ = D * ‖φ‖ := mul_comm _ _

theorem dualRenormEquiv_symm_norm_le (e : E ≃L[ℝ] F) {D : ℝ} (hD : 0 ≤ D)
    (he : ‖e.toContinuousLinearMap‖ ≤ D) :
    ‖(dualRenormEquiv e).symm.toContinuousLinearMap‖ ≤ D :=
  dualRenormEquiv_norm_le e.symm hD he

theorem submoduleMap_norm_le (e : E ≃L[ℝ] F) (S : Submodule ℝ E)
    {D : ℝ} (hD : 0 ≤ D) (he : ‖e.toContinuousLinearMap‖ ≤ D) :
    ‖(e.submoduleMap S).toContinuousLinearMap‖ ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro x
  change ‖e (x : E)‖ ≤ D * ‖(x : E)‖
  exact (e.toContinuousLinearMap.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right he (norm_nonneg (x : E)))

theorem submoduleMap_symm_norm_le (e : E ≃L[ℝ] F) (S : Submodule ℝ E)
    {D : ℝ} (hD : 0 ≤ D) (he : ‖e.symm.toContinuousLinearMap‖ ≤ D) :
    ‖(e.submoduleMap S).symm.toContinuousLinearMap‖ ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro x
  change ‖e.symm (x : F)‖ ≤ D * ‖(x : F)‖
  exact (e.symm.toContinuousLinearMap.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right he (norm_nonneg (x : F)))

theorem HasHilbertNormWithin.pullback_contraction {D η : ℝ} (hD : 0 ≤ D)
    (e : E ≃L[ℝ] F) (he : ‖e.toContinuousLinearMap‖ ≤ 1)
    (hei : ‖e.symm.toContinuousLinearMap‖ ≤ D) (hF : HasHilbertNormWithin F η) :
    HasHilbertNormWithin E (D * η) := by
  obtain ⟨p, hp⟩ := hF.exists_model
  let A := (p.equivOfBounds η hp).toLinearMap.comp e.toLinearMap
  apply hasHilbertNormWithin_of_hilbert_embedding A
  intro x
  have heupper : ‖e x‖ ≤ ‖x‖ := (e.toContinuousLinearMap.le_opNorm x).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg x))
  have helower : ‖x‖ ≤ D * ‖e x‖ := by
    calc
      ‖x‖ = ‖e.symm (e x)‖ := congrArg norm (e.symm_apply_apply x).symm
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right hei (norm_nonneg _)
  change p.q (e x) ≤ ‖x‖ ∧ ‖x‖ ≤ (D * η) * p.q (e x)
  exact ⟨(hp (e x)).1.trans heupper, helower.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hp (e x)).2 hD)⟩

theorem localHilbert_pullback_contraction {D η : ℝ} (hD : 0 ≤ D) {d : ℕ}
    (e : E ≃L[ℝ] F) (he : ‖e.toContinuousLinearMap‖ ≤ 1)
    (hei : ‖e.symm.toContinuousLinearMap‖ ≤ D)
    (hF : ∀ (T : Submodule ℝ F) [FiniteDimensional ℝ T],
      Module.finrank ℝ T ≤ d → HasHilbertNormWithin T η)
    (S : Submodule ℝ E) [FiniteDimensional ℝ S] (hS : Module.finrank ℝ S ≤ d) :
    HasHilbertNormWithin S (D * η) := by
  let T := S.map e.toLinearMap
  let f : S ≃L[ℝ] T := e.submoduleMap S
  letI : FiniteDimensional ℝ T := FiniteDimensional.of_injective f.symm.toLinearMap f.symm.injective
  have hT : Module.finrank ℝ T ≤ d := f.toLinearEquiv.finrank_eq.symm.trans_le hS
  exact (hF T hT).pullback_contraction hD f
    (submoduleMap_norm_le e S zero_le_one he) (submoduleMap_symm_norm_le e S hD hei)

/-- Dual subspace geometry transports with the bounds reversed once. -/
theorem DualSubspacesLocallyHilbertWithin.pullback {D η : ℝ} (hD : 0 ≤ D) {d : ℕ}
    (e : E ≃L[ℝ] F) (he : ‖e.toContinuousLinearMap‖ ≤ D)
    (hei : ‖e.symm.toContinuousLinearMap‖ ≤ 1)
    (hF : DualSubspacesLocallyHilbertWithin F d η) :
    DualSubspacesLocallyHilbertWithin E d (D * η) := by
  intro V S _ hS
  let V₀ := V.map e.toLinearMap
  let f : V ≃L[ℝ] V₀ := e.submoduleMap V
  have hf : ‖f.toContinuousLinearMap‖ ≤ D := submoduleMap_norm_le e V hD he
  have hfi : ‖f.symm.toContinuousLinearMap‖ ≤ 1 := submoduleMap_symm_norm_le e V zero_le_one hei
  exact localHilbert_pullback_contraction hD (dualRenormEquiv f)
    (dualRenormEquiv_norm_le f zero_le_one hfi)
    (dualRenormEquiv_symm_norm_le f hD hf) (hF V₀) S hS

theorem parallelogram_dual_subspace_localHilbert {ν η : ℝ} {d : ℕ}
    (hgood : ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G],
      ApproxParallelogram (fun x : G => ‖x‖) ν → LocallyHilbertWithin G d η)
    (hpar : ApproxParallelogram (fun x : E => ‖x‖) ν) :
    DualSubspacesLocallyHilbertWithin E d η := by
  intro V
  exact hgood (StrongDual ℝ V) (hpar.subspace V).dual

/-- Version accepting an already chosen local threshold, for the recursive
parameter construction. -/
theorem renorm_dual_subspace_dual_localHilbert {D ν η : ℝ} {d : ℕ} (hD : 0 ≤ D)
    (hgood : ∀ (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G],
      ApproxParallelogram (fun x : G => ‖x‖) ν → LocallyHilbertWithin G d η)
    (e : E ≃L[ℝ] F) (he : ‖e.toContinuousLinearMap‖ ≤ 1)
    (hei : ‖e.symm.toContinuousLinearMap‖ ≤ D)
    (hpar : ApproxParallelogram (fun x : F => ‖x‖) ν) :
    DualSubspacesLocallyHilbertWithin (StrongDual ℝ E) d (D * η) := by
  exact (parallelogram_dual_subspace_localHilbert hgood hpar.dual).pullback hD
    (dualRenormEquiv e) (dualRenormEquiv_norm_le e hD hei)
    (dualRenormEquiv_symm_norm_le e zero_le_one he)

theorem exists_parallelogram_dual_subspace_threshold (d : ℕ) {η : ℝ} (hη : 1 < η) :
    ∃ ν > 1, ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
      ApproxParallelogram (fun x : E => ‖x‖) ν →
        DualSubspacesLocallyHilbertWithin E d η := by
  obtain ⟨ν, hν, hgood⟩ := exists_localHilbert_subspace_threshold d hη
  refine ⟨ν, hν, ?_⟩
  intro E _ _ hpar V
  have hV : ApproxParallelogram (fun x : V => ‖x‖) ν := hpar.subspace V
  exact hgood (StrongDual ℝ V) hV.dual

/-- A global approximate-parallelogram renorming controls small subspaces of
the dual of every dual subspace. The subspace itself need not be small. -/
theorem exists_renorm_dual_subspace_dual_threshold (d : ℕ) {η : ℝ} (hη : 1 < η) :
    ∃ ν > 1, ∀ (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F],
      ∀ {D : ℝ}, 0 ≤ D → ∀ (e : E ≃L[ℝ] F),
      ‖e.toContinuousLinearMap‖ ≤ 1 → ‖e.symm.toContinuousLinearMap‖ ≤ D →
      ApproxParallelogram (fun x : F => ‖x‖) ν →
      DualSubspacesLocallyHilbertWithin (StrongDual ℝ E) d (D * η) := by
  obtain ⟨ν, hν, hgood⟩ := exists_parallelogram_dual_subspace_threshold d hη
  refine ⟨ν, hν, ?_⟩
  intro E F _ _ _ _ D hD e he hei hpar
  exact (hgood (StrongDual ℝ F) hpar.dual).pullback hD (dualRenormEquiv e)
    (dualRenormEquiv_norm_le e hD hei) (dualRenormEquiv_symm_norm_le e zero_le_one he)

end ComplementedSubspace
