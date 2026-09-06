import ComplementedSubspace.AmbientProjection

/-! The actual range profile of a diagonal projection, over any normed field. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

def lpSubmoduleIsometryScalar (S : ∀ i, Submodule 𝕜 (E i)) :
    lp (fun i => S i) 2 →ₗᵢ[𝕜] lp E 2 where
  toFun x := ⟨fun i => (x i : E i), (lp.memℓp x).mono' (fun _ => le_rfl)⟩
  map_add' x y := by ext i; rfl
  map_smul' r x := by ext i; rfl
  norm_map' x := le_antisymm
    (lp.norm_mono (by norm_num) (fun _ => le_rfl))
    (lp.norm_mono (by norm_num) (fun _ => le_rfl))

@[simp] theorem lpSubmoduleIsometryScalar_apply (S : ∀ i, Submodule 𝕜 (E i))
    (x : lp (fun i => S i) 2) (i : ι) : lpSubmoduleIsometryScalar S x i = (x i : E i) := rfl

theorem lpSubmoduleIsometryScalar_range_eq_diagonal (P : ∀ i, E i →L[𝕜] E i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i) :
    (lpSubmoduleIsometryScalar (fun i => (P i).range)).toLinearMap.range =
      (lpDiagonal 2 P hC hP).range := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    refine ⟨lpSubmoduleIsometryScalar (fun i => (P i).range) y, ?_⟩
    ext i
    change P i (y i : E i) = (y i : E i)
    obtain ⟨z, hz⟩ := (y i).property
    rw [← hz]
    exact congrArg (fun T : E i →L[𝕜] E i => T z) (hIdem i)
  · rintro x ⟨y, rfl⟩
    let z : lp (fun i => (P i).range) 2 :=
      ⟨fun i => ⟨P i (y i), ⟨y i, rfl⟩⟩,
        (lp.memℓp (lpDiagonal 2 P hC hP y)).mono' (fun _ => le_rfl)⟩
    exact ⟨z, rfl⟩

def lpDiagonalRangeEquivScalar (P : ∀ i, E i →L[𝕜] E i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i) :
    lp (fun i => (P i).range) 2 ≃ₗᵢ[𝕜] (lpDiagonal 2 P hC hP).range :=
  (lpSubmoduleIsometryScalar (fun i => (P i).range)).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (lpSubmoduleIsometryScalar_range_eq_diagonal P hC hP hIdem))

@[simp] theorem lpDiagonalRangeEquivScalar_apply (P : ∀ i, E i →L[𝕜] E i)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i)
    (x : lp (fun i => (P i).range) 2) (i : ι) :
    (lpDiagonalRangeEquivScalar P hC hP hIdem x : lp E 2) i = (x i : E i) := rfl

end ComplementedSubspace
