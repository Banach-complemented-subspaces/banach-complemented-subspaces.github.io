import ComplementedSubspace.DPRtoGL

/-!
# Finiteness of finite-dimensional unconditional constants

The coordinate map of a finite basis gives an explicit finite bound for every
admissible multiplier. Consequently every finite-dimensional real normed space
has both forms of local unconditional structure defined in the manuscript.
-/

noncomputable section
open scoped NNReal ENNReal

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pi_multiplier_norm_le {n : ℕ} (θ x : Fin n → ℝ)
    (hθ : ∀ i, ‖θ i‖ ≤ 1) : ‖fun i => θ i * x i‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hθ i) (norm_nonneg _)).trans
    (by simpa only [one_mul] using norm_le_pi_norm x i)

theorem norm_basisMultiplier_apply_le_equivFunL {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) (θ : Fin n → ℝ)
    (hθ : ∀ i, ‖θ i‖ ≤ 1) (x : E) :
    ‖basisMultiplier b θ x‖ ≤
      (‖b.equivFunL.symm.toContinuousLinearMap‖ *
        ‖b.equivFunL.toContinuousLinearMap‖) * ‖x‖ := by
  have heq : basisMultiplier b θ x =
      b.equivFunL.symm (fun i => θ i * b.equivFunL x i) := by
    have hcoord (y : E) : b.equivFunL y = b.equivFun y := by
      ext i
      exact b.equivFunL_apply y i
    apply b.equivFunL.injective
    rw [b.equivFunL.apply_symm_apply, hcoord, hcoord]
    have h := basisMultiplier_equivFun_symm b θ (b.equivFun x)
    rw [b.equivFun.symm_apply_apply] at h
    rw [h, b.equivFun.apply_symm_apply]
  rw [heq]
  calc
    ‖b.equivFunL.symm (fun i => θ i * b.equivFunL x i)‖ ≤
        ‖b.equivFunL.symm.toContinuousLinearMap‖ *
          ‖fun i => θ i * b.equivFunL x i‖ :=
      b.equivFunL.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖b.equivFunL.symm.toContinuousLinearMap‖ * ‖b.equivFunL x‖ :=
      mul_le_mul_of_nonneg_left (pi_multiplier_norm_le θ _ hθ) (norm_nonneg _)
    _ ≤ ‖b.equivFunL.symm.toContinuousLinearMap‖ *
        (‖b.equivFunL.toContinuousLinearMap‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (b.equivFunL.toContinuousLinearMap.le_opNorm x)
        (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

theorem unconditionalBasisConstant_le_equivFunL {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) :
    unconditionalBasisConstant b ≤
      max 1 ((‖b.equivFunL.symm.toContinuousLinearMap‖₊ *
        ‖b.equivFunL.toContinuousLinearMap‖₊ : ℝ≥0) : ℝ≥0∞) := by
  apply max_le (le_max_left _ _)
  refine iSup_le fun θ => iSup_le fun hθ => ?_
  apply le_trans _ (le_max_right _ _)
  apply enorm_le_coe.mpr
  apply NNReal.coe_le_coe.mp
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact norm_basisMultiplier_apply_le_equivFunL b θ hθ

theorem unconditionalBasisConstant_lt_top {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) : unconditionalBasisConstant b < ⊤ :=
  (unconditionalBasisConstant_le_equivFunL b).trans_lt
    (max_lt (by simp) ENNReal.coe_lt_top)

theorem unconditionalConstant_lt_top [FiniteDimensional ℝ E] :
    unconditionalConstant E < ⊤ := by
  have h : unconditionalConstant E ≤
      unconditionalBasisConstant (Module.finBasis ℝ E) :=
    iInf_le_of_le (Module.finrank ℝ E) (iInf_le_of_le (Module.finBasis ℝ E) le_rfl)
  exact h.trans_lt (unconditionalBasisConstant_lt_top (Module.finBasis ℝ E))

theorem chiDPR_le_unconditionalConstant_top [FiniteDimensional ℝ E] :
    chiDPR E ≤ unconditionalConstant ↥(⊤ : Submodule ℝ E) := by
  refine iSup_le fun V => iSup_le fun _ => iSup_le fun _ => ?_
  exact lambdaDPR_le_of_le E (show V ≤ (⊤ : Submodule ℝ E) from le_top) inferInstance

theorem lambdaDPR_top [FiniteDimensional ℝ E] :
    lambdaDPR E ⊤ = unconditionalConstant ↥(⊤ : Submodule ℝ E) := by
  apply le_antisymm (lambdaDPR_le_of_le E le_rfl inferInstance)
  refine le_iInf fun F => le_iInf fun hF => le_iInf fun _ => ?_
  have h : F = ⊤ := top_unique hF
  subst F
  exact le_rfl

/-- For a nonzero finite-dimensional space, its largest finite subspace already
attains the outer DPR supremum. The infimum over bases need not be attained. -/
theorem chiDPR_eq_unconditionalConstant_top [FiniteDimensional ℝ E] [Nontrivial E] :
    chiDPR E = unconditionalConstant ↥(⊤ : Submodule ℝ E) := by
  apply le_antisymm chiDPR_le_unconditionalConstant_top
  rw [← lambdaDPR_top]
  exact le_iSup_of_le (⊤ : Submodule ℝ E)
    (le_iSup_of_le (inferInstance : FiniteDimensional ℝ ↥(⊤ : Submodule ℝ E))
      (le_iSup_of_le (top_ne_bot : (⊤ : Submodule ℝ E) ≠ ⊥) le_rfl))

theorem finiteDimensional_hasDPRLocalUnconditionalStructure [FiniteDimensional ℝ E] :
    HasDPRLocalUnconditionalStructure E :=
  chiDPR_le_unconditionalConstant_top.trans_lt unconditionalConstant_lt_top

theorem finiteDimensional_hasGLLocalUnconditionalStructure [FiniteDimensional ℝ E] :
    HasGLLocalUnconditionalStructure E :=
  finiteDimensional_hasDPRLocalUnconditionalStructure.hasGLLocalUnconditionalStructure

end ComplementedSubspace
