import ComplementedSubspace.SelectedHilbertReplacement

/-! # Exact decomposition of a superspace containing a distinguished block

If the ambient space splits into two summands, a subspace containing the first
summand splits into that summand and its own image in the second summand.
All maps below use the inherited norms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace
namespace SuperspaceSplitting

variable {E W Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

variable (F : Submodule ℝ Z)
  (I : E →L[ℝ] Z) (R : Z →L[ℝ] E) (J : W →L[ℝ] Z) (S : Z →L[ℝ] W)
  (hIF : I.range ≤ F)
  (hJS : J.comp S = ContinuousLinearMap.id ℝ Z - I.comp R)

def inclusion : E →L[ℝ] F := I.codRestrict F (fun x => hIF ⟨x, rfl⟩)

def first : F →L[ℝ] E := R.comp F.subtypeL

def second : F →L[ℝ] (F.map S.toLinearMap) := selectedTailMap F S

include hIF hJS in
theorem tail_mem (w : F.map S.toLinearMap) : J (w : W) ∈ F := by
  obtain ⟨z, hz, hsz⟩ := w.property
  have heq : J (S z) = z - I (R z) :=
    congrArg (fun T : Z →L[ℝ] Z => T z) hJS
  change S z = (w : W) at hsz
  rw [← hsz, heq]
  exact F.sub_mem hz (hIF ⟨R z, rfl⟩)

def tailInclusion : (F.map S.toLinearMap) →L[ℝ] F :=
  (J.comp (F.map S.toLinearMap).subtypeL).codRestrict F (tail_mem F I R J S hIF hJS)

@[simp] theorem inclusion_coe (x : E) :
    (inclusion F I hIF x : Z) = I x := rfl

@[simp] theorem first_apply (z : F) : first F R z = R z := rfl

@[simp] theorem second_coe (z : F) : (second F S z : W) = S z := rfl

@[simp] theorem tailInclusion_coe (w : F.map S.toLinearMap) :
    (tailInclusion F I R J S hIF hJS w : Z) = J (w : W) := rfl

theorem first_inclusion (hRI : R.comp I = ContinuousLinearMap.id ℝ E) :
    (first F R).comp (inclusion F I hIF) = ContinuousLinearMap.id ℝ E := by
  ext x
  exact congrArg (fun T : E →L[ℝ] E => T x) hRI

theorem tail_second :
    (tailInclusion F I R J S hIF hJS).comp (second F S) =
      ContinuousLinearMap.id ℝ F - (inclusion F I hIF).comp (first F R) := by
  ext z
  exact congrArg (fun T : Z →L[ℝ] Z => T (z : Z)) hJS

theorem norm_sq_decomposition
    (hdec : ∀ z : Z, ‖z‖ ^ 2 = ‖R z‖ ^ 2 + ‖S z‖ ^ 2) (z : F) :
    ‖z‖ ^ 2 = ‖first F R z‖ ^ 2 + ‖second F S z‖ ^ 2 := hdec z

theorem inclusion_contracts (hI : ∀ x, ‖I x‖ ≤ ‖x‖) (x : E) :
    ‖inclusion F I hIF x‖ ≤ ‖x‖ := hI x

theorem first_contracts (hR : ∀ x, ‖R x‖ ≤ ‖x‖) (z : F) :
    ‖first F R z‖ ≤ ‖z‖ := hR z

theorem second_contracts (hS : ∀ x, ‖S x‖ ≤ ‖x‖) (z : F) :
    ‖second F S z‖ ≤ ‖z‖ := hS z

theorem tailInclusion_contracts (hJ : ∀ x, ‖J x‖ ≤ ‖x‖)
    (w : F.map S.toLinearMap) :
    ‖tailInclusion F I R J S hIF hJS w‖ ≤ ‖w‖ := hJ w

end SuperspaceSplitting
end ComplementedSubspace
