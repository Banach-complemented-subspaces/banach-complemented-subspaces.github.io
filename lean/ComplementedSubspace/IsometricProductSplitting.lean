import ComplementedSubspace.NormSqSplitting

/-! The four contractive maps of an isometric two-term lp2 product. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace
namespace IsometricProductSplitting

variable {E W Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (e : Z ≃ₗᵢ[ℝ] WithLp 2 (E × W))

def inclusion : E →L[ℝ] Z :=
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E W).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ E W))

def first : Z →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E W).comp e.toContinuousLinearEquiv.toContinuousLinearMap

def tailInclusion : W →L[ℝ] Z :=
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E W).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ E W))

def second : Z →L[ℝ] W :=
  (WithLp.sndL 2 ℝ E W).comp e.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem inclusion_apply (x : E) :
    inclusion e x = e.symm (WithLp.toLp 2 (x, 0)) := rfl

@[simp] theorem tailInclusion_apply (w : W) :
    tailInclusion e w = e.symm (WithLp.toLp 2 (0, w)) := rfl

@[simp] theorem first_apply (z : Z) : first e z = (e z).fst := rfl
@[simp] theorem second_apply (z : Z) : second e z = (e z).snd := rfl

theorem first_inclusion : (first e).comp (inclusion e) = ContinuousLinearMap.id ℝ E := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, inclusion_apply, first_apply,
    LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.id_apply]
  rfl

theorem first_tailInclusion (w : W) : first e (tailInclusion e w) = 0 := by
  change (e (e.symm (WithLp.toLp 2 (0, w)))).fst = 0
  rw [e.apply_symm_apply]
  rfl

theorem second_tailInclusion (w : W) : second e (tailInclusion e w) = w := by
  change (e (e.symm (WithLp.toLp 2 (0, w)))).snd = w
  rw [e.apply_symm_apply]
  rfl

theorem tail_second : (tailInclusion e).comp (second e) =
    ContinuousLinearMap.id ℝ Z - (inclusion e).comp (first e) := by
  ext z
  apply e.injective
  change e (e.symm (WithLp.toLp 2 (0, (e z).snd))) =
    e (z - e.symm (WithLp.toLp 2 ((e z).fst, 0)))
  rw [map_sub, e.apply_symm_apply, e.apply_symm_apply]
  apply WithLp.ofLp_injective
  change ((0 : E), (e z).ofLp.2) = (e z).ofLp - ((e z).ofLp.1, (0 : W))
  ext <;> simp

theorem norm_sq (z : Z) : ‖z‖ ^ 2 = ‖first e z‖ ^ 2 + ‖second e z‖ ^ 2 := by
  rw [← e.norm_map z]
  exact WithLp.prod_norm_sq_eq_of_L2 (e z)

theorem inclusion_contracts (x : E) : ‖inclusion e x‖ ≤ ‖x‖ := by
  rw [inclusion_apply, e.symm.norm_map, WithLp.norm_toLp_fst]

theorem tailInclusion_contracts (w : W) : ‖tailInclusion e w‖ ≤ ‖w‖ := by
  rw [tailInclusion_apply, e.symm.norm_map, WithLp.norm_toLp_snd]

theorem first_contracts (z : Z) : ‖first e z‖ ≤ ‖z‖ := by
  have h := norm_sq e z
  nlinarith [norm_nonneg z, norm_nonneg (first e z), sq_nonneg ‖second e z‖]

theorem second_contracts (z : Z) : ‖second e z‖ ≤ ‖z‖ := by
  have h := norm_sq e z
  nlinarith [norm_nonneg z, norm_nonneg (second e z), sq_nonneg ‖first e z‖]

end IsometricProductSplitting
end ComplementedSubspace
