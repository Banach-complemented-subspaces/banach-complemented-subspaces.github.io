import ComplementedSubspace.LocalHilbertDual
import ComplementedSubspace.LocalHilbert
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Combining a Hilbertian head and a locally Hilbertian tail

The actual two-term lp2 norm is used throughout. A pair of Hilbert norm models
combines into their Hilbert lp2 product. This preserves the larger distortion,
rather than introducing a loss depending on the dimensions of the two pieces.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem HasHilbertNormWithin.mono {D D' : ℝ} (h : HasHilbertNormWithin E D)
    (hDD' : D ≤ D') : HasHilbertNormWithin E D' := by
  obtain ⟨q, hdef, hpar, hcomp⟩ := h
  refine ⟨q, hdef, hpar, fun x => ⟨(hcomp x).1, ?_⟩⟩
  exact (hcomp x).2.trans (mul_le_mul_of_nonneg_right hDD' (apply_nonneg q x))

/-- Pulling back a genuine Hilbert norm along a linear embedding. -/
theorem hasHilbertNormWithin_of_hilbert_embedding
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {D : ℝ} (A : E →ₗ[ℝ] H)
    (hA : ∀ x : E, ‖A x‖ ≤ ‖x‖ ∧ ‖x‖ ≤ D * ‖A x‖) :
    HasHilbertNormWithin E D := by
  let q : Seminorm ℝ E := (normSeminorm ℝ H).comp A
  refine ⟨q, ?_, ?_, hA⟩
  · intro x hx
    have h := (hA x).2
    change ‖A x‖ = 0 at hx
    rw [hx, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg x))
  · intro x y
    change ‖A (x + y)‖ ^ 2 + ‖A (x - y)‖ ^ 2 =
      2 * (‖A x‖ ^ 2 + ‖A y‖ ^ 2)
    simpa only [map_add, map_sub] using parallelogram_law_with_norm ℝ (A x) (A y)

/-- A norm-squared decomposition combines Hilbert models with no extra loss. -/
theorem hasHilbertNormWithin_of_norm_sq_sum {D : ℝ} (hD : 0 ≤ D)
    (hF : HasHilbertNormWithin F D) (hG : HasHilbertNormWithin G D)
    (A : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G)
    (hsq : ∀ x : E, ‖x‖ ^ 2 = ‖A x‖ ^ 2 + ‖B x‖ ^ 2) :
    HasHilbertNormWithin E D := by
  obtain ⟨p, hp⟩ := hF.exists_model
  obtain ⟨q, hq⟩ := hG.exists_model
  let a : E →ₗ[ℝ] p.Space := (p.equivOfBounds D hp).toLinearMap.comp A
  let b : E →ₗ[ℝ] q.Space := (q.equivOfBounds D hq).toLinearMap.comp B
  let T : E →ₗ[ℝ] WithLp 2 (p.Space × q.Space) :=
    (WithLp.linearEquiv 2 ℝ (p.Space × q.Space)).symm.toLinearMap.comp (a.prod b)
  have hT (x : E) : ‖T x‖ ^ 2 = p.q (A x) ^ 2 + q.q (B x) ^ 2 := by
    exact WithLp.prod_norm_sq_eq_of_L2 (T x)
  apply hasHilbertNormWithin_of_hilbert_embedding T
  intro x
  have hp0 := apply_nonneg p.q (A x)
  have hq0 := apply_nonneg q.q (B x)
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    calc
      ‖T x‖ ^ 2 = p.q (A x) ^ 2 + q.q (B x) ^ 2 := hT x
      _ ≤ ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := add_le_add
        ((sq_le_sq₀ hp0 (norm_nonneg _)).mpr (hp (A x)).1)
        ((sq_le_sq₀ hq0 (norm_nonneg _)).mpr (hq (B x)).1)
      _ = ‖x‖ ^ 2 := (hsq x).symm
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (norm_nonneg _))).mp
    calc
      ‖x‖ ^ 2 = ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := hsq x
      _ ≤ (D * p.q (A x)) ^ 2 + (D * q.q (B x)) ^ 2 := add_le_add
        ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD hp0)).mpr (hp (A x)).2)
        ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD hq0)).mpr (hq (B x)).2)
      _ = (D * ‖T x‖) ^ 2 := by simp only [mul_pow, hT]; ring

theorem HasHilbertNormWithin.prodL2 {D : ℝ} (hD : 0 ≤ D)
    (hF : HasHilbertNormWithin F D) (hG : HasHilbertNormWithin G D) :
    HasHilbertNormWithin (WithLp 2 (F × G)) D :=
  hasHilbertNormWithin_of_norm_sq_sum hD hF hG
    (WithLp.fstₗ 2 ℝ F G) (WithLp.sndₗ 2 ℝ F G)
    (fun x => WithLp.prod_norm_sq_eq_of_L2 x)

/-- Restricting a Hilbert norm to a subspace preserves its distortion. -/
theorem HasHilbertNormWithin.subspace {D : ℝ} (h : HasHilbertNormWithin E D)
    (S : Submodule ℝ E) : HasHilbertNormWithin S D := by
  obtain ⟨p, hp⟩ := h.exists_model
  apply hasHilbertNormWithin_of_hilbert_embedding
    ((p.equivOfBounds D hp).toLinearMap.comp S.subtype)
  intro x
  exact hp x

/-- The head may have arbitrary dimension. Only the tail image of the small
subspace must be locally Hilbertian. -/
theorem localHilbert_prodL2 {d : ℕ} {D : ℝ} (hD : 2 ≤ D)
    (hF : HasHilbertNormWithin F D)
    (hG : ∀ (S : Submodule ℝ G) [FiniteDimensional ℝ S],
      Module.finrank ℝ S ≤ d → HasHilbertNormWithin S 2)
    (S : Submodule ℝ (WithLp 2 (F × G))) [FiniteDimensional ℝ S]
    (hS : Module.finrank ℝ S ≤ d) : HasHilbertNormWithin S D := by
  let A : S →L[ℝ] F := (WithLp.fstL 2 ℝ F G).comp S.subtypeL
  let B : S →L[ℝ] G := (WithLp.sndL 2 ℝ F G).comp S.subtypeL
  have hB : HasHilbertNormWithin ↥B.range D :=
    (hG B.range ((LinearMap.finrank_range_le B.toLinearMap).trans hS)).mono hD
  apply hasHilbertNormWithin_of_norm_sq_sum (by linarith : 0 ≤ D) hF hB
    A.toLinearMap B.rangeRestrict.toLinearMap
  intro x
  exact WithLp.prod_norm_sq_eq_of_L2 (x : WithLp 2 (F × G))

/-- Constant one in the norm parallelogram inequality is the exact identity. -/
theorem ApproxParallelogram.norm_eq_of_one
    (h : ApproxParallelogram (fun x : E => ‖x‖) 1) (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h₁ := h x y
  have h₂ := h (x + y) (x - y)
  dsimp only at h₁ h₂
  have hx : (x + y) + (x - y) = (2 : ℝ) • x := by module
  have hy : (x + y) - (x - y) = (2 : ℝ) • y := by module
  rw [hx, hy, norm_smul, norm_smul] at h₂
  norm_num at h₁ h₂
  nlinarith

/-- A Hilbert norm comparison passes to the continuous real dual with exactly
the same distortion. The dual Hilbert norm is obtained from our direct dual
parallelogram theorem, without a reflexivity or Riesz-representation assumption. -/
theorem HasHilbertNormWithin.dual {D : ℝ} (hD : 0 < D)
    (h : HasHilbertNormWithin E D) : HasHilbertNormWithin (StrongDual ℝ E) D := by
  obtain ⟨p, hp⟩ := h.exists_model
  let e := p.equivOfBounds D hp
  have hpar : ApproxParallelogram (fun x : p.Space => ‖x‖) 1 := by
    intro x y
    simpa only [mul_one] using (parallelogram_law_with_norm ℝ x y).le
  have hdual := hpar.dual
  letI : InnerProductSpace ℝ (StrongDual ℝ p.Space) :=
    InnerProductSpace.ofNorm (𝕜 := ℝ) (fun φ ψ => by
      simpa only [pow_two] using hdual.norm_eq_of_one φ ψ)
  let U : StrongDual ℝ E →L[ℝ] StrongDual ℝ p.Space :=
    ContinuousLinearMap.precomp ℝ e.symm.toContinuousLinearMap
  let A : StrongDual ℝ E →ₗ[ℝ] StrongDual ℝ p.Space := D⁻¹ • U.toLinearMap
  have he : ‖e.toContinuousLinearMap‖ ≤ 1 := p.norm_equivOfBounds_le D hp
  have hei : ‖e.symm.toContinuousLinearMap‖ ≤ D := p.norm_equivOfBounds_symm_le hD.le hp
  have hUupper (φ : StrongDual ℝ E) : ‖U φ‖ ≤ D * ‖φ‖ := by
    calc
      ‖U φ‖ ≤ ‖φ‖ * ‖e.symm.toContinuousLinearMap‖ := φ.opNorm_comp_le _
      _ ≤ ‖φ‖ * D := mul_le_mul_of_nonneg_left hei (norm_nonneg φ)
      _ = D * ‖φ‖ := mul_comm _ _
  have hUlower (φ : StrongDual ℝ E) : ‖φ‖ ≤ ‖U φ‖ := by
    have hback : (U φ).comp e.toContinuousLinearMap = φ := by
      ext x
      change φ (e.symm (e x)) = φ x
      rw [e.symm_apply_apply]
    calc
      ‖φ‖ = ‖(U φ).comp e.toContinuousLinearMap‖ := congrArg norm hback.symm
      _ ≤ ‖U φ‖ * ‖e.toContinuousLinearMap‖ := (U φ).opNorm_comp_le _
      _ ≤ ‖U φ‖ * 1 := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = ‖U φ‖ := mul_one _
  have hAnorm (φ : StrongDual ℝ E) : ‖A φ‖ = D⁻¹ * ‖U φ‖ := by
    change ‖D⁻¹ • U φ‖ = D⁻¹ * ‖U φ‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hD)]
  apply hasHilbertNormWithin_of_hilbert_embedding A
  intro φ
  rw [hAnorm]
  constructor
  · calc
      D⁻¹ * ‖U φ‖ ≤ D⁻¹ * (D * ‖φ‖) :=
        mul_le_mul_of_nonneg_left (hUupper φ) (inv_nonneg.2 hD.le)
      _ = ‖φ‖ := by field_simp
  · calc
      ‖φ‖ ≤ ‖U φ‖ := hUlower φ
      _ = D * (D⁻¹ * ‖U φ‖) := by field_simp

theorem HasHilbertNormWithin.bidual {D : ℝ} (hD : 0 < D)
    (h : HasHilbertNormWithin E D) :
    HasHilbertNormWithin (StrongDual ℝ (StrongDual ℝ E)) D :=
  (h.dual hD).dual hD

/-- The qualitative local-Hilbert threshold for an arbitrary head/tail product. -/
theorem exists_localHilbert_prodL2_threshold (d : ℕ) {D : ℝ} (hD : 2 ≤ D) :
    ∃ ν > 1, ∀ (F G : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G],
      HasHilbertNormWithin F D → ApproxParallelogram (fun x : G => ‖x‖) ν →
      ∀ (S : Submodule ℝ (WithLp 2 (F × G))) [FiniteDimensional ℝ S],
        Module.finrank ℝ S ≤ d → HasHilbertNormWithin S D := by
  obtain ⟨ν, hν, hgood⟩ := exists_localHilbert_subspace_threshold d (D := 2) (by norm_num)
  refine ⟨ν, hν, ?_⟩
  intro F G _ _ _ _ hF hG S _ hS
  exact localHilbert_prodL2 hD hF (hgood G hG) S hS

end ComplementedSubspace
