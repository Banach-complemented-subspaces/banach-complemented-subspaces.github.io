import ComplementedSubspace.LocalHilbertSum

/-! # Isometric restriction of local Hilbert estimates -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem HasHilbertNormWithin.of_linearIsometry {D : ℝ}
    (h : HasHilbertNormWithin W D) (e : E →ₗᵢ[ℝ] W) :
    HasHilbertNormWithin E D := by
  obtain ⟨q, hdef, hpar, hbound⟩ := h
  refine ⟨q.comp e.toLinearMap, ?_, ?_, ?_⟩
  · intro x hx
    apply e.injective
    simpa only [map_zero] using hdef (e x) hx
  · intro x y
    change q (e (x + y)) ^ 2 + q (e (x - y)) ^ 2 = 2 * (q (e x) ^ 2 + q (e y) ^ 2)
    rw [map_add, map_sub]
    exact hpar (e x) (e y)
  · intro x
    change q (e x) ≤ ‖x‖ ∧ ‖x‖ ≤ D * q (e x)
    simpa only [LinearIsometry.norm_map] using hbound (e x)

theorem localHilbert_of_linearIsometry {q : ℕ} {D : ℝ}
    (hlocal : ∀ (V : Submodule ℝ W) [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ q → HasHilbertNormWithin V D)
    (e : E →ₗᵢ[ℝ] W) (S : Submodule ℝ E) [FiniteDimensional ℝ S]
    (hS : Module.finrank ℝ S ≤ q) : HasHilbertNormWithin S D := by
  let V := S.map e.toLinearMap
  let f : S →ₗᵢ[ℝ] V :=
    { toLinearMap := (e.toLinearMap.comp S.subtype).codRestrict V
        (fun x => ⟨x, x.property, rfl⟩)
      norm_map' x := e.norm_map x }
  have hV : Module.finrank ℝ V ≤ q := (Submodule.finrank_map_le e.toLinearMap S).trans hS
  exact (hlocal V hV).of_linearIsometry f

theorem localHilbert_subspace {q : ℕ} {D : ℝ}
    (hlocal : ∀ (V : Submodule ℝ W) [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ q → HasHilbertNormWithin V D)
    (S : Submodule ℝ W) (V : Submodule ℝ S) [FiniteDimensional ℝ V]
    (hV : Module.finrank ℝ V ≤ q) : HasHilbertNormWithin V D :=
  localHilbert_of_linearIsometry hlocal S.subtypeₗᵢ V hV

end ComplementedSubspace
