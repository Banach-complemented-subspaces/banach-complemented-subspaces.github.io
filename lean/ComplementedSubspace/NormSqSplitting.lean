import ComplementedSubspace.FiniteSuperspaceSplitting

/-! Exact linear isometries for squared-norm direct sums. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {E W Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def normSqSplitEquiv
    (I : E →L[ℝ] Z) (R : Z →L[ℝ] E) (J : W →L[ℝ] Z) (S : Z →L[ℝ] W)
    (hRI : ∀ x, R (I x) = x) (hSI : ∀ x, S (I x) = 0)
    (hRJ : ∀ w, R (J w) = 0) (hSJ : ∀ w, S (J w) = w)
    (hsplit : ∀ z, I (R z) + J (S z) = z)
    (hsq : ∀ z, ‖z‖ ^ 2 = ‖R z‖ ^ 2 + ‖S z‖ ^ 2) :
    Z ≃ₗᵢ[ℝ] WithLp 2 (E × W) where
  toFun z := WithLp.toLp 2 (R z, S z)
  invFun z := I z.fst + J z.snd
  left_inv := hsplit
  right_inv z := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · change R (I z.fst + J z.snd) = z.ofLp.1
      rw [map_add, hRI, hRJ, add_zero]
      rfl
    · change S (I z.fst + J z.snd) = z.ofLp.2
      rw [map_add, hSI, hSJ, zero_add]
      rfl
  map_add' x y := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> exact map_add _ x y
  map_smul' c x := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> exact map_smul _ c x
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact (hsq z).symm

theorem normSqSplit_second_inclusion_zero
    (I : E →L[ℝ] Z) (R : Z →L[ℝ] E) (S : Z →L[ℝ] W)
    (hRI : R.comp I = ContinuousLinearMap.id ℝ E)
    (hI : ∀ x, ‖I x‖ ≤ ‖x‖)
    (hsq : ∀ z, ‖z‖ ^ 2 = ‖R z‖ ^ 2 + ‖S z‖ ^ 2) (x : E) : S (I x) = 0 := by
  have hr : R (I x) = x := congrArg (fun T : E →L[ℝ] E => T x) hRI
  have hh := hsq (I x)
  rw [hr] at hh
  have hi := hI x
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (I x), norm_nonneg x, norm_nonneg (S (I x))]

namespace SuperspaceSplitting

def equiv (F : Submodule ℝ Z)
    (I : E →L[ℝ] Z) (R : Z →L[ℝ] E) (J : W →L[ℝ] Z) (S : Z →L[ℝ] W)
    (hIF : I.range ≤ F)
    (hRI : R.comp I = ContinuousLinearMap.id ℝ E)
    (hJS : J.comp S = ContinuousLinearMap.id ℝ Z - I.comp R)
    (hRJ : ∀ w, R (J w) = 0) (hSJ : ∀ w, S (J w) = w)
    (hI : ∀ x, ‖I x‖ ≤ ‖x‖)
    (hsq : ∀ z, ‖z‖ ^ 2 = ‖R z‖ ^ 2 + ‖S z‖ ^ 2) :
    F ≃ₗᵢ[ℝ] WithLp 2 (E × F.map S.toLinearMap) := by
  refine normSqSplitEquiv (inclusion F I hIF) (first F R)
    (tailInclusion F I R J S hIF hJS) (second F S) ?_ ?_ ?_ ?_ ?_
    (norm_sq_decomposition F R S hsq)
  · intro x
    exact congrArg (fun T : E →L[ℝ] E => T x) hRI
  · intro x
    apply Subtype.ext
    exact normSqSplit_second_inclusion_zero I R S hRI hI hsq x
  · intro w
    exact hRJ w
  · intro w
    apply Subtype.ext
    exact hSJ w
  · intro z
    apply Subtype.ext
    have h := congrArg (fun T : Z →L[ℝ] Z => T (z : Z)) hJS
    change I (R z) + J (S z) = (z : Z)
    change J (S z) = (z : Z) - I (R z) at h
    rw [h, add_sub_cancel]

end SuperspaceSplitting
end ComplementedSubspace
