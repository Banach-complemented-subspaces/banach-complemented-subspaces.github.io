import ComplementedSubspace.LocalUnconditional

/-!
# Unconditional renorming and the comparison of local structure constants

This file constructs the supremum-of-multiplier-norms renorming and proves
`chiGL Z ≤ chiDPR Z`. Each finite superspace with a bounded unconditional basis
constant supplies an explicit GL factorisation. Passing to the infima requires
no assumption that an optimal basis, superspace, or factorisation exists.
-/

noncomputable section
open scoped NNReal ENNReal

namespace ComplementedSubspace

abbrev MultiplierBall (n : ℕ) := {θ : Fin n → ℝ // ∀ i, ‖θ i‖ ≤ 1}

instance multiplierBallInhabited (n : ℕ) : Inhabited (MultiplierBall n) :=
  ⟨⟨fun _ => 1, fun _ => by simp⟩⟩

def MultiplierBall.mul {n : ℕ} (θ η : MultiplierBall n) : MultiplierBall n :=
  ⟨fun i => θ.1 i * η.1 i, fun i => by
    rw [norm_mul]
    exact (mul_le_mul (θ.2 i) (η.2 i) (norm_nonneg _) zero_le_one).trans (by simp)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} (b : Module.Basis (Fin n) ℝ E)

theorem basisMultiplier_one : basisMultiplier b (fun _ => 1) =
    ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro i
  change basisMultiplier b (fun _ => 1) (b i) = b i
  rw [basisMultiplier_apply_basis, one_smul]

theorem basisMultiplier_comp (θ η : Fin n → ℝ) :
    (basisMultiplier b θ).comp (basisMultiplier b η) =
      basisMultiplier b (fun i => θ i * η i) := by
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro i
  change basisMultiplier b θ (basisMultiplier b η (b i)) =
    basisMultiplier b (fun j => θ j * η j) (b i)
  rw [basisMultiplier_apply_basis, map_smul, basisMultiplier_apply_basis,
    basisMultiplier_apply_basis, smul_smul, mul_comm]

theorem norm_basisMultiplier_le_bound (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    (θ : MultiplierBall n) (x : E) :
    ‖basisMultiplier b θ.1 x‖ ≤ (C : ℝ) * ‖x‖ := by
  have he : ‖basisMultiplier b θ.1‖ₑ ≤ (C : ℝ≥0∞) :=
    (enorm_basisMultiplier_le b θ.1 θ.2).trans hb
  have hn : ‖basisMultiplier b θ.1‖₊ ≤ C := enorm_le_coe.mp he
  have hr : ‖basisMultiplier b θ.1‖ ≤ (C : ℝ) := NNReal.coe_le_coe.mpr hn
  exact ((basisMultiplier b θ.1).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg x))

def multiplierSeminorm (θ : MultiplierBall n) : Seminorm ℝ E :=
  (normSeminorm ℝ E).comp (basisMultiplier b θ.1).toLinearMap

def unconditionalRenorm : Seminorm ℝ E := ⨆ θ : MultiplierBall n, multiplierSeminorm b θ

theorem multiplierSeminorm_bddAbove (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) :
    BddAbove (Set.range (multiplierSeminorm b)) := by
  refine ⟨C • normSeminorm ℝ E, ?_⟩
  rintro _ ⟨θ, rfl⟩ x
  exact norm_basisMultiplier_le_bound b C hb θ x

theorem multiplierNorm_bddAbove (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) (x : E) :
    BddAbove (Set.range fun θ : MultiplierBall n => ‖basisMultiplier b θ.1 x‖) := by
  refine ⟨(C : ℝ) * ‖x‖, ?_⟩
  rintro _ ⟨θ, rfl⟩
  exact norm_basisMultiplier_le_bound b C hb θ x

theorem unconditionalRenorm_apply (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) (x : E) :
    unconditionalRenorm b x = ⨆ θ : MultiplierBall n, ‖basisMultiplier b θ.1 x‖ := by
  rw [unconditionalRenorm, Seminorm.iSup_apply (multiplierSeminorm_bddAbove b C hb)]
  rfl

theorem unconditionalRenorm_le (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) (x : E) :
    unconditionalRenorm b x ≤ (C : ℝ) * ‖x‖ := by
  rw [unconditionalRenorm_apply b C hb]
  exact ciSup_le fun θ => norm_basisMultiplier_le_bound b C hb θ x

theorem norm_le_unconditionalRenorm (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) (x : E) :
    ‖x‖ ≤ unconditionalRenorm b x := by
  rw [unconditionalRenorm_apply b C hb]
  have h := le_ciSup (multiplierNorm_bddAbove b C hb x)
    (⟨fun _ => 1, fun _ => by simp⟩ : MultiplierBall n)
  simpa only [basisMultiplier_one, ContinuousLinearMap.id_apply] using h

/-- All admissible coordinate multipliers are contractive for the new norm. -/
theorem unconditionalRenorm_multiplier_le (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    (θ : MultiplierBall n) (x : E) :
    unconditionalRenorm b (basisMultiplier b θ.1 x) ≤ unconditionalRenorm b x := by
  rw [unconditionalRenorm_apply b C hb]
  apply ciSup_le
  intro η
  have hcomp : basisMultiplier b η.1 (basisMultiplier b θ.1 x) =
      basisMultiplier b (η.mul θ).1 x :=
    congrArg (fun T : E →L[ℝ] E => T x) (basisMultiplier_comp b η.1 θ.1)
  rw [hcomp, unconditionalRenorm_apply b C hb]
  exact le_ciSup (multiplierNorm_bddAbove b C hb x) (η.mul θ)

section LocalConstants

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A finite superspace with a `C`-unconditional basis yields a GL
factorisation through its unconditional renorming, of cost `C`. -/
def GLFactorization.ofContainingBasis {V F : Submodule ℝ Z} (hVF : V ≤ F)
    {n : ℕ} (b : Module.Basis (Fin n) ℝ ↥F) (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) : GLFactorization V where
  dimension := n
  auxNorm := (unconditionalRenorm b).comp b.equivFun.symm.toLinearMap
  positive_definite := by
    intro x hx
    change unconditionalRenorm b (b.equivFun.symm x) = 0 at hx
    have hn : ‖b.equivFun.symm x‖ ≤ 0 :=
      (norm_le_unconditionalRenorm b C hb _).trans_eq hx
    have hz : b.equivFun.symm x = 0 :=
      norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    apply b.equivFun.symm.injective
    simpa only [map_zero] using hz
  unconditional := by
    intro θ x hθ
    change unconditionalRenorm b (b.equivFun.symm (fun i => θ i * x i)) ≤
      unconditionalRenorm b (b.equivFun.symm x)
    rw [← basisMultiplier_equivFun_symm]
    exact unconditionalRenorm_multiplier_le b C hb ⟨θ, hθ⟩ _
  a := b.equivFun.toLinearMap.comp (Submodule.inclusion hVF)
  b := F.subtype.comp b.equivFun.symm.toLinearMap
  factorizes := by
    ext x
    change ((b.equivFun.symm (b.equivFun (Submodule.inclusion hVF x)) : ↥F) : Z) =
      (x : Z)
    rw [b.equivFun.symm_apply_apply]
    rfl
  aBound := C
  bBound := 1
  bound_a := by
    intro x
    change unconditionalRenorm b
      (b.equivFun.symm (b.equivFun (Submodule.inclusion hVF x))) ≤ (C : ℝ) * ‖x‖
    rw [b.equivFun.symm_apply_apply]
    exact unconditionalRenorm_le b C hb (Submodule.inclusion hVF x)
  bound_b := by
    intro x
    change ‖b.equivFun.symm x‖ ≤ (1 : ℝ) * unconditionalRenorm b (b.equivFun.symm x)
    rw [one_mul]
    exact norm_le_unconditionalRenorm b C hb _

@[simp]
theorem GLFactorization.ofContainingBasis_cost {V F : Submodule ℝ Z} (hVF : V ≤ F)
    {n : ℕ} (b : Module.Basis (Fin n) ℝ ↥F) (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) :
    (GLFactorization.ofContainingBasis hVF b C hb).cost = (C : ℝ≥0∞) := by
  change (C : ℝ≥0∞) * 1 = (C : ℝ≥0∞)
  exact mul_one _

/-- The local GL infimum is bounded by each basis constant of every finite
superspace. The infinity case needs no finite bound or factorisation choice. -/
theorem lambdaGL_le_unconditionalBasisConstant {V F : Submodule ℝ Z} (hVF : V ≤ F)
    {n : ℕ} (b : Module.Basis (Fin n) ℝ ↥F) :
    lambdaGL Z V ≤ unconditionalBasisConstant b := by
  by_cases htop : unconditionalBasisConstant b = ⊤
  · rw [htop]
    exact le_top
  let C := (unconditionalBasisConstant b).toNNReal
  have hC : (C : ℝ≥0∞) = unconditionalBasisConstant b := ENNReal.coe_toNNReal htop
  have hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞) := hC.symm.le
  calc
    lambdaGL Z V ≤ (GLFactorization.ofContainingBasis hVF b C hb).cost :=
      lambdaGL_le_cost Z _
    _ = (C : ℝ≥0∞) := GLFactorization.ofContainingBasis_cost hVF b C hb
    _ = unconditionalBasisConstant b := hC

theorem lambdaGL_le_unconditionalConstant {V F : Submodule ℝ Z} (hVF : V ≤ F) :
    lambdaGL Z V ≤ unconditionalConstant ↥F := by
  exact le_iInf fun n => le_iInf fun b =>
    lambdaGL_le_unconditionalBasisConstant hVF b

/-- Passage to both infima is valid even when neither is attained. -/
theorem lambdaGL_le_lambdaDPR (V : Submodule ℝ Z) :
    lambdaGL Z V ≤ lambdaDPR Z V := by
  exact le_iInf fun F => le_iInf fun hVF => le_iInf fun _ =>
    lambdaGL_le_unconditionalConstant hVF

/-- The comparison in the manuscript's preliminaries: GL local unconditional
structure is quantitatively weaker than DPR local unconditional structure. -/
theorem chiGL_le_chiDPR (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    chiGL Z ≤ chiDPR Z := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hV0 => ?_
  exact (lambdaGL_le_lambdaDPR V).trans (le_iSup_of_le V
    (le_iSup_of_le hV (le_iSup_of_le hV0 le_rfl)))

theorem HasDPRLocalUnconditionalStructure.hasGLLocalUnconditionalStructure
    (h : HasDPRLocalUnconditionalStructure Z) : HasGLLocalUnconditionalStructure Z :=
  lt_of_le_of_lt (chiGL_le_chiDPR Z) h

end LocalConstants

end ComplementedSubspace
