import ComplementedSubspace.UnconditionalHilbertSynthesis
import Mathlib.LinearAlgebra.Basis.SMul

/-! Independent rescaling normalizes a finite basis in its actual Hilbert
image without changing any coordinate multiplier. The sign-average estimates
then give bounded synthesis and coordinate operators on Euclidean space. -/

noncomputable section
open scoped BigOperators ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem basisMultiplier_isUnitSMul {m : ℕ} (b : Module.Basis (Fin m) ℝ E)
    {w : Fin m → ℝ} (hw : ∀ i, IsUnit (w i)) (θ : Fin m → ℝ) :
    basisMultiplier (b.isUnitSMul hw) θ = basisMultiplier b θ := by
  apply ContinuousLinearMap.coe_injective
  apply (b.isUnitSMul hw).ext
  intro i
  change basisMultiplier (b.isUnitSMul hw) θ ((b.isUnitSMul hw) i) =
    basisMultiplier b θ ((b.isUnitSMul hw) i)
  rw [basisMultiplier_apply_basis, Module.Basis.isUnitSMul_apply,
    map_smul, basisMultiplier_apply_basis]
  exact smul_comm _ _ _

theorem unconditionalBasisConstant_isUnitSMul {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) {w : Fin m → ℝ} (hw : ∀ i, IsUnit (w i)) :
    unconditionalBasisConstant (b.isUnitSMul hw) = unconditionalBasisConstant b := by
  simp only [unconditionalBasisConstant, basisMultiplier_isUnitSMul]

theorem basis_hilbert_image_norm_pos {m : ℕ} (b : Module.Basis (Fin m) ℝ E)
    (T : E ≃L[ℝ] H) (i : Fin m) : 0 < ‖T (b i)‖ := by
  apply norm_pos_iff.mpr
  intro h
  exact b.ne_zero i (T.injective (h.trans T.map_zero.symm))

def hilbertNormalizedBasis {m : ℕ} (b : Module.Basis (Fin m) ℝ E)
    (T : E ≃L[ℝ] H) : Module.Basis (Fin m) ℝ E :=
  b.isUnitSMul (w := fun i => ‖T (b i)‖⁻¹)
    (fun i => isUnit_iff_ne_zero.mpr (inv_ne_zero (basis_hilbert_image_norm_pos b T i).ne'))

theorem hilbertNormalizedBasis_apply {m : ℕ} (b : Module.Basis (Fin m) ℝ E)
    (T : E ≃L[ℝ] H) (i : Fin m) :
    hilbertNormalizedBasis b T i = ‖T (b i)‖⁻¹ • b i :=
  Module.Basis.isUnitSMul_apply _ _

theorem hilbertNormalizedBasis_norm {m : ℕ} (b : Module.Basis (Fin m) ℝ E)
    (T : E ≃L[ℝ] H) (i : Fin m) : ‖T (hilbertNormalizedBasis b T i)‖ = 1 := by
  rw [hilbertNormalizedBasis_apply, map_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (basis_hilbert_image_norm_pos b T i).ne']

theorem hilbertNormalizedBasis_constant {m : ℕ} (b : Module.Basis (Fin m) ℝ E)
    (T : E ≃L[ℝ] H) :
    unconditionalBasisConstant (hilbertNormalizedBasis b T) = unconditionalBasisConstant b :=
  unconditionalBasisConstant_isUnitSMul b _

theorem exists_hilbert_normalized_basis {m : ℕ} (b : Module.Basis (Fin m) ℝ E)
    (T : E ≃L[ℝ] H) :
    ∃ c : Module.Basis (Fin m) ℝ E,
      unconditionalBasisConstant c = unconditionalBasisConstant b ∧
      ∀ i, ‖T (c i)‖ = 1 :=
  ⟨hilbertNormalizedBasis b T, hilbertNormalizedBasis_constant b T,
    hilbertNormalizedBasis_norm b T⟩

/-- Synthesis as a linear equivalence, with genuine Euclidean domain norm. -/
def basisHilbertSynthesisLinearEquiv {m : ℕ} (b : Module.Basis (Fin m) ℝ E)
    (T : E ≃L[ℝ] H) : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] H :=
  (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).trans (b.equivFun.symm.trans T.toLinearEquiv)

@[simp] theorem basisHilbertSynthesisLinearEquiv_apply {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (T : E ≃L[ℝ] H)
    (a : EuclideanSpace ℝ (Fin m)) :
    basisHilbertSynthesisLinearEquiv b T a = T (b.equivFun.symm (WithLp.ofLp a)) := rfl

/-- The actual synthesis equivalence, with continuity certified by the two
sign-average estimates rather than a nonquantitative finite-dimensional theorem. -/
def basisHilbertSynthesisEquiv {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (T : E ≃L[ℝ] H)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ x, ‖T x‖ ≤ ‖x‖) (hhi : ∀ x, ‖x‖ ≤ D * ‖T x‖)
    (hnorm : ∀ i, ‖T (b i)‖ = 1) : EuclideanSpace ℝ (Fin m) ≃L[ℝ] H := by
  let e := basisHilbertSynthesisLinearEquiv b T
  exact e.toContinuousLinearEquivOfBounds (K * D) (K * D)
    (fun a => (unconditional_hilbert_synthesis_bounds b T K hb hD hlo hhi hnorm
      (WithLp.ofLp a)).1)
    (fun y => by
      have h := (unconditional_hilbert_synthesis_bounds b T K hb hD hlo hhi hnorm
        (WithLp.ofLp (e.symm y))).2
      change ‖e.symm y‖ ≤ (K : ℝ) * D * ‖e (e.symm y)‖ at h
      simpa only [e.apply_symm_apply] using h)

@[simp] theorem basisHilbertSynthesisEquiv_apply {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (T : E ≃L[ℝ] H)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ x, ‖T x‖ ≤ ‖x‖) (hhi : ∀ x, ‖x‖ ≤ D * ‖T x‖)
    (hnorm : ∀ i, ‖T (b i)‖ = 1) (a : EuclideanSpace ℝ (Fin m)) :
    basisHilbertSynthesisEquiv b T K hb hD hlo hhi hnorm a =
      T (b.equivFun.symm (WithLp.ofLp a)) := rfl

theorem norm_basisHilbertSynthesisEquiv_le {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (T : E ≃L[ℝ] H)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ x, ‖T x‖ ≤ ‖x‖) (hhi : ∀ x, ‖x‖ ≤ D * ‖T x‖)
    (hnorm : ∀ i, ‖T (b i)‖ = 1) :
    ‖(basisHilbertSynthesisEquiv b T K hb hD hlo hhi hnorm).toContinuousLinearMap‖ ≤ K * D := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg K.2 hD)
  intro a
  exact (unconditional_hilbert_synthesis_bounds b T K hb hD hlo hhi hnorm (WithLp.ofLp a)).1

theorem norm_basisHilbertSynthesisEquiv_symm_le {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (T : E ≃L[ℝ] H)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ x, ‖T x‖ ≤ ‖x‖) (hhi : ∀ x, ‖x‖ ≤ D * ‖T x‖)
    (hnorm : ∀ i, ‖T (b i)‖ = 1) :
    ‖(basisHilbertSynthesisEquiv b T K hb hD hlo hhi hnorm).symm.toContinuousLinearMap‖ ≤ K * D := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg K.2 hD)
  intro y
  let e := basisHilbertSynthesisEquiv b T K hb hD hlo hhi hnorm
  change ‖e.symm y‖ ≤ (K : ℝ) * D * ‖y‖
  have h := (unconditional_hilbert_synthesis_bounds b T K hb hD hlo hhi hnorm
    (WithLp.ofLp (e.symm y))).2
  change ‖e.symm y‖ ≤ (K : ℝ) * D * ‖e (e.symm y)‖ at h
  simpa only [e.apply_symm_apply] using h

theorem exists_normalized_hilbert_synthesis {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (T : E ≃L[ℝ] H)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ x, ‖T x‖ ≤ ‖x‖) (hhi : ∀ x, ‖x‖ ≤ D * ‖T x‖) :
    ∃ c : Module.Basis (Fin m) ℝ E, ∃ U : EuclideanSpace ℝ (Fin m) ≃L[ℝ] H,
      unconditionalBasisConstant c = unconditionalBasisConstant b ∧
      (∀ i, ‖T (c i)‖ = 1) ∧
      (∀ a, U a = T (c.equivFun.symm (WithLp.ofLp a))) ∧
      ‖U.toContinuousLinearMap‖ ≤ K * D ∧
      ‖U.symm.toContinuousLinearMap‖ ≤ K * D := by
  let c := hilbertNormalizedBasis b T
  have hc : unconditionalBasisConstant c ≤ (K : ℝ≥0∞) :=
    (hilbertNormalizedBasis_constant b T).le.trans hb
  have hn := hilbertNormalizedBasis_norm b T
  exact ⟨c, basisHilbertSynthesisEquiv c T K hc hD hlo hhi hn,
    hilbertNormalizedBasis_constant b T, hn,
    basisHilbertSynthesisEquiv_apply c T K hc hD hlo hhi hn,
    norm_basisHilbertSynthesisEquiv_le c T K hc hD hlo hhi hn,
    norm_basisHilbertSynthesisEquiv_symm_le c T K hc hD hlo hhi hn⟩

end ComplementedSubspace
