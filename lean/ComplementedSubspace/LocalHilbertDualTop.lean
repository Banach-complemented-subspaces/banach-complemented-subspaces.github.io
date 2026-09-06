import ComplementedSubspace.LocalHilbertProperty
import ComplementedSubspace.LocalHilbertSumDual
import ComplementedSubspace.LocalHilbertTransport

/-! Recover local dual geometry by taking the whole-space submodule. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

theorem DualSubspacesLocallyHilbertWithin.dual {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ} {D : ℝ}
    (h : DualSubspacesLocallyHilbertWithin E d D) :
    LocallyHilbertWithin (StrongDual ℝ E) d D := by
  let e : StrongDual ℝ (⊤ : Submodule ℝ E) ≃ₗᵢ[ℝ] StrongDual ℝ E :=
    realDualIsometryEquiv (LinearIsometryEquiv.ofTop E (⊤ : Submodule ℝ E) rfl)
  exact localHilbert_of_linearIsometry (h ⊤) e.symm.toLinearIsometry

theorem locallyHilbert_bidual_of_dualSubspaces {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ} {D : ℝ}
    (h : DualSubspacesLocallyHilbertWithin (StrongDual ℝ E) d D) :
    LocallyHilbertWithin (StrongDual ℝ (StrongDual ℝ E)) d D := h.dual

end ComplementedSubspace
