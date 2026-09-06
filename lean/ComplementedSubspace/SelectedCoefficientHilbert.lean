import ComplementedSubspace.FrameCoefficientHilbert
import ComplementedSubspace.NormalizedHilbertSynthesis
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The coefficient-Hilbert identification on the actual two-term sum. -/
noncomputable section
open scoped BigOperators ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

namespace ComplementedSubspace

section General
variable {E E₂ H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def hilbertCoefficientProductEquiv (e : E ≃L[ℝ] E₂) :
    WithLp 2 (E × H) ≃L[ℝ] WithLp 2 (E₂ × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E H).trans
    ((e.prodCongr (ContinuousLinearEquiv.refl ℝ H)).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ E₂ H).symm)

@[simp] theorem hilbertCoefficientProductEquiv_fst (e : E ≃L[ℝ] E₂)
    (z : WithLp 2 (E × H)) :
    (hilbertCoefficientProductEquiv (H := H) e z).fst = e z.fst := rfl

@[simp] theorem hilbertCoefficientProductEquiv_snd (e : E ≃L[ℝ] E₂)
    (z : WithLp 2 (E × H)) :
    (hilbertCoefficientProductEquiv (H := H) e z).snd = z.snd := rfl

theorem hilbertCoefficientProductEquiv_contracts (e : E ≃L[ℝ] E₂)
    (hlo : ∀ x, ‖e x‖ ≤ ‖x‖) (z : WithLp 2 (E × H)) :
    ‖hilbertCoefficientProductEquiv (H := H) e z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [WithLp.prod_norm_sq_eq_of_L2, hilbertCoefficientProductEquiv_fst,
    hilbertCoefficientProductEquiv_snd]
  exact add_le_add ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hlo z.fst)) le_rfl

theorem hilbertCoefficientProductEquiv_lower_bound (e : E ≃L[ℝ] E₂)
    {D : ℝ} (hD : 1 ≤ D) (hhi : ∀ x, ‖x‖ ≤ D * ‖e x‖)
    (z : WithLp 2 (E × H)) :
    ‖z‖ ≤ D * ‖hilbertCoefficientProductEquiv (H := H) e z‖ := by
  have hD₀ : 0 ≤ D := by linarith
  have hx := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD₀ (norm_nonneg _))).mpr (hhi z.fst)
  have hy : ‖z.snd‖ ^ 2 ≤ D ^ 2 * ‖z.snd‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ D ^ 2 - 1 by nlinarith) (sq_nonneg ‖z.snd‖)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD₀ (norm_nonneg _))).mp
  simp only [mul_pow, WithLp.prod_norm_sq_eq_of_L2,
    hilbertCoefficientProductEquiv_fst, hilbertCoefficientProductEquiv_snd] at *
  nlinarith

/-- The selected image is a subspace of the actual coefficient Hilbert product. -/
def selectedCoefficientHilbertSpace (e : E ≃L[ℝ] E₂)
    (F : Submodule ℝ (WithLp 2 (E × H))) : Submodule ℝ (WithLp 2 (E₂ × H)) :=
  F.map (hilbertCoefficientProductEquiv (H := H) e).toLinearEquiv.toLinearMap

def selectedCoefficientHilbertEquiv (e : E ≃L[ℝ] E₂)
    (F : Submodule ℝ (WithLp 2 (E × H))) :
    F ≃L[ℝ] selectedCoefficientHilbertSpace e F :=
  (hilbertCoefficientProductEquiv (H := H) e).submoduleMap F

@[simp] theorem selectedCoefficientHilbertEquiv_coe (e : E ≃L[ℝ] E₂)
    (F : Submodule ℝ (WithLp 2 (E × H))) (z : F) :
    (selectedCoefficientHilbertEquiv e F z : WithLp 2 (E₂ × H)) =
      hilbertCoefficientProductEquiv (H := H) e z := rfl

theorem selectedCoefficientHilbertEquiv_contracts (e : E ≃L[ℝ] E₂)
    (F : Submodule ℝ (WithLp 2 (E × H))) (hlo : ∀ x, ‖e x‖ ≤ ‖x‖) (z : F) :
    ‖selectedCoefficientHilbertEquiv e F z‖ ≤ ‖z‖ := by
  change ‖hilbertCoefficientProductEquiv (H := H) e (z : WithLp 2 (E × H))‖ ≤
    ‖(z : WithLp 2 (E × H))‖
  exact hilbertCoefficientProductEquiv_contracts (H := H) e hlo (z : WithLp 2 (E × H))

theorem selectedCoefficientHilbertEquiv_lower_bound (e : E ≃L[ℝ] E₂)
    (F : Submodule ℝ (WithLp 2 (E × H))) {D : ℝ} (hD : 1 ≤ D)
    (hhi : ∀ x, ‖x‖ ≤ D * ‖e x‖) (z : F) :
    ‖z‖ ≤ D * ‖selectedCoefficientHilbertEquiv e F z‖ := by
  change ‖(z : WithLp 2 (E × H))‖ ≤
    D * ‖hilbertCoefficientProductEquiv (H := H) e (z : WithLp 2 (E × H))‖
  exact hilbertCoefficientProductEquiv_lower_bound (H := H) e hD hhi (z : WithLp 2 (E × H))

theorem selectedCoefficientHilbertSpace_finrank (e : E ≃L[ℝ] E₂)
    (F : Submodule ℝ (WithLp 2 (E × H))) :
    Module.finrank ℝ (selectedCoefficientHilbertSpace e F) = Module.finrank ℝ F :=
  (selectedCoefficientHilbertEquiv e F).toLinearEquiv.finrank_eq.symm

/-- The return map remains exactly the first coordinate. -/
theorem selectedCoefficientHilbertEquiv_first_projection (e : E ≃L[ℝ] E₂)
    (F : Submodule ℝ (WithLp 2 (E × H))) (B : F →L[ℝ] E)
    (hB : ∀ z : F, B z = (z : WithLp 2 (E × H)).fst) (z : F) :
    e (B z) = (selectedCoefficientHilbertEquiv e F z : WithLp 2 (E₂ × H)).fst := by
  rw [hB]
  rfl

end General

section Frame
variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem one_le_realFrameHilbertScale (n : ℕ) (p : ℝ) (hp : 2 ≤ p) :
    1 ≤ realFrameHilbertScale n p := by
  rw [realFrameHilbertScale_eq]
  apply Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
  apply mul_nonneg (Nat.cast_nonneg n)
  have hdiv : 1 / p ≤ (1 : ℝ) / 2 := one_div_le_one_div_of_le (by norm_num) hp
  linarith

theorem frameSelectedCoefficientHilbert_bounds (hp : 2 ≤ p)
    (F : Submodule ℝ (WithLp 2 (FrameCoefficient n p × H))) (z : F) :
    ‖selectedCoefficientHilbertEquiv (frameCoefficientHilbertEquiv n p) F z‖ ≤ ‖z‖ ∧
      ‖z‖ ≤ realFrameHilbertScale n p *
        ‖selectedCoefficientHilbertEquiv (frameCoefficientHilbertEquiv n p) F z‖ :=
  ⟨selectedCoefficientHilbertEquiv_contracts _ F (frameCoefficient_hilbert_lower n p hp) z,
    selectedCoefficientHilbertEquiv_lower_bound _ F (one_le_realFrameHilbertScale n p hp)
      (frameCoefficient_hilbert_upper n p hp) z⟩

end Frame
end ComplementedSubspace
