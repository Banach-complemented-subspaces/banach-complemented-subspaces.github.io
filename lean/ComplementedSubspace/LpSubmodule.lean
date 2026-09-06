import ComplementedSubspace.AmbientProjection
import ComplementedSubspace.LpTwoUniformConvex

/-! Exact inherited range profiles and coordinate square-norm splittings. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]

/-- Coordinatewise inclusion of inherited subspaces preserves the outer lp2 norm. -/
def lpSubmoduleIsometry (S : ∀ i, Submodule ℝ (E i)) :
    lp (fun i => S i) 2 →ₗᵢ[ℝ] lp E 2 where
  toFun x := ⟨fun i => (x i : E i), (lp.memℓp x).mono' (fun _ => le_rfl)⟩
  map_add' x y := by ext i; rfl
  map_smul' r x := by ext i; rfl
  norm_map' x := le_antisymm
    (lp.norm_mono (by norm_num) (fun _ => le_rfl))
    (lp.norm_mono (by norm_num) (fun _ => le_rfl))

@[simp] theorem lpSubmoduleIsometry_apply (S : ∀ i, Submodule ℝ (E i))
    (x : lp (fun i => S i) 2) (i : ι) : lpSubmoduleIsometry S x i = (x i : E i) := rfl

theorem lpSubmoduleIsometry_range_eq_diagonal (P : ∀ i, E i →L[ℝ] E i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i) :
    (lpSubmoduleIsometry (fun i => (P i).range)).toLinearMap.range =
      (lpDiagonal 2 P hC hP).range := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    refine ⟨lpSubmoduleIsometry (fun i => (P i).range) y, ?_⟩
    ext i
    change P i (y i : E i) = (y i : E i)
    obtain ⟨z, hz⟩ := (y i).property
    rw [← hz]
    exact congrArg (fun T : E i →L[ℝ] E i => T z) (hIdem i)
  · rintro x ⟨y, rfl⟩
    let z : lp (fun i => (P i).range) 2 :=
      ⟨fun i => ⟨P i (y i), ⟨y i, rfl⟩⟩,
        (lp.memℓp (lpDiagonal 2 P hC hP y)).mono' (fun _ => le_rfl)⟩
    exact ⟨z, rfl⟩

/-- The actual range of a diagonal projection is exactly the lp2 sum of its
coordinate ranges, all equipped with their inherited norms. -/
def lpDiagonalRangeEquiv (P : ∀ i, E i →L[ℝ] E i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i) :
    lp (fun i => (P i).range) 2 ≃ₗᵢ[ℝ] (lpDiagonal 2 P hC hP).range :=
  (lpSubmoduleIsometry (fun i => (P i).range)).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (lpSubmoduleIsometry_range_eq_diagonal P hC hP hIdem))

@[simp] theorem lpDiagonalRangeEquiv_apply (P : ∀ i, E i →L[ℝ] E i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i)
    (x : lp (fun i => (P i).range) 2) (i : ι) :
    (lpDiagonalRangeEquiv P hC hP hIdem x : lp E 2) i = (x i : E i) := rfl

theorem lp_two_coordinate_norm_sq [DecidableEq ι] (x : lp E 2) (i : ι) :
    ‖x‖ ^ 2 = ‖x i‖ ^ 2 + ‖x - lp.single 2 i (x i)‖ ^ 2 := by
  have hs := (lp_two_hasSum_sq (lp.single 2 i (x i))).add
    (lp_two_hasSum_sq (x - lp.single 2 i (x i)))
  have heq : (fun j => ‖lp.single 2 i (x i) j‖ ^ 2 +
      ‖(x - lp.single 2 i (x i)) j‖ ^ 2) = (fun j => ‖x j‖ ^ 2) := by
    funext j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [heq] at hs
  have h := (lp_two_hasSum_sq x).unique hs
  simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using h

section RangeCoordinates
variable [DecidableEq ι] (P : ∀ i, E i →L[ℝ] E i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i)

def lpDiagonalRangeSingle (i : ι) : (P i).range →L[ℝ] (lpDiagonal 2 P hC hP).range :=
  (lpDiagonalRangeEquiv P hC hP hIdem).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (lp.singleContinuousLinearMap ℝ (fun j => (P j).range) 2 i)

def lpDiagonalRangeEval (i : ι) : (lpDiagonal 2 P hC hP).range →L[ℝ] (P i).range :=
  (lp.evalCLM ℝ (fun j => (P j).range) 2 i).comp
    (lpDiagonalRangeEquiv P hC hP hIdem).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem lpDiagonalRangeEval_single (i : ι) (x : (P i).range) :
    lpDiagonalRangeEval P hC hP hIdem i (lpDiagonalRangeSingle P hC hP hIdem i x) = x := by
  change ((lpDiagonalRangeEquiv P hC hP hIdem).symm
    ((lpDiagonalRangeEquiv P hC hP hIdem) (lp.single 2 i x))) i = x
  rw [LinearIsometryEquiv.symm_apply_apply]
  simp

@[simp] theorem lpDiagonalRangeSingle_norm (i : ι) (x : (P i).range) :
    ‖lpDiagonalRangeSingle P hC hP hIdem i x‖ = ‖x‖ := by
  change ‖lpDiagonalRangeEquiv P hC hP hIdem (lp.single 2 i x)‖ = ‖x‖
  rw [LinearIsometryEquiv.norm_map, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

theorem lpDiagonalRangeEval_norm_le (i : ι) : ‖lpDiagonalRangeEval P hC hP hIdem i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖((lpDiagonalRangeEquiv P hC hP hIdem).symm x) i‖ ≤ 1 * ‖x‖
  simpa only [one_mul, LinearIsometryEquiv.norm_map] using
    lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      ((lpDiagonalRangeEquiv P hC hP hIdem).symm x) i

theorem lpDiagonalRange_coordinate_norm_sq (x : (lpDiagonal 2 P hC hP).range) (i : ι) :
    ‖x‖ ^ 2 = ‖lpDiagonalRangeEval P hC hP hIdem i x‖ ^ 2 +
      ‖x - lpDiagonalRangeSingle P hC hP hIdem i (lpDiagonalRangeEval P hC hP hIdem i x)‖ ^ 2 := by
  let e := lpDiagonalRangeEquiv P hC hP hIdem
  have h := lp_two_coordinate_norm_sq (e.symm x) i
  have hres : e (e.symm x - lp.single 2 i ((e.symm x) i)) =
      x - lpDiagonalRangeSingle P hC hP hIdem i (lpDiagonalRangeEval P hC hP hIdem i x) := by
    rw [map_sub, e.apply_symm_apply]
    rfl
  rw [← hres, e.norm_map, e.symm.norm_map] at *
  exact h

/-- The complementary component belongs to the exact kernel of block evaluation. -/
def lpDiagonalRangeRemainder (i : ι) :
    (lpDiagonal 2 P hC hP).range →L[ℝ] (lpDiagonalRangeEval P hC hP hIdem i).ker :=
  (ContinuousLinearMap.id ℝ (lpDiagonal 2 P hC hP).range -
    (lpDiagonalRangeSingle P hC hP hIdem i).comp
      (lpDiagonalRangeEval P hC hP hIdem i)).codRestrict _ (by
        intro x
        change lpDiagonalRangeEval P hC hP hIdem i
          (x - lpDiagonalRangeSingle P hC hP hIdem i
            (lpDiagonalRangeEval P hC hP hIdem i x)) = 0
        rw [map_sub, lpDiagonalRangeEval_single, sub_self])

theorem lpDiagonalRange_split_norm_sq (x : (lpDiagonal 2 P hC hP).range) (i : ι) :
    ‖x‖ ^ 2 = ‖lpDiagonalRangeEval P hC hP hIdem i x‖ ^ 2 +
      ‖lpDiagonalRangeRemainder P hC hP hIdem i x‖ ^ 2 :=
  lpDiagonalRange_coordinate_norm_sq P hC hP hIdem x i

theorem lpDiagonalRangeRemainder_apply_norm_le (i : ι) (x : (lpDiagonal 2 P hC hP).range) :
    ‖lpDiagonalRangeRemainder P hC hP hIdem i x‖ ≤ ‖x‖ := by
  have h := lpDiagonalRange_split_norm_sq P hC hP hIdem x i
  have hx := norm_nonneg x
  have hr := norm_nonneg (lpDiagonalRangeRemainder P hC hP hIdem i x)
  nlinarith only [h, hx, hr, sq_nonneg (‖lpDiagonalRangeEval P hC hP hIdem i x‖)]

end RangeCoordinates

end ComplementedSubspace
