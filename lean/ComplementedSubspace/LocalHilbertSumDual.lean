import ComplementedSubspace.LocalHilbertSum
import ComplementedSubspace.LocalHilbertProperty

/-!
# The real dual of an actual two-term lp2 sum

Restriction to the two coordinate inclusions has the exact sum-of-squares
dual norm. This directly supplies the local Hilbert head/tail decomposition
for dual spaces, without any reflexivity assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256

namespace ComplementedSubspace

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private lemma dual_cross_eval_sq_le (f : StrongDual ℝ E) (g : StrongDual ℝ F)
    (x : E) (y : F) :
    (f x + g y) ^ 2 ≤ (‖f‖ ^ 2 + ‖g‖ ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hf : |f x| ≤ ‖f‖ * ‖x‖ := by simpa only [Real.norm_eq_abs] using f.le_opNorm x
  have hg : |g y| ≤ ‖g‖ * ‖y‖ := by simpa only [Real.norm_eq_abs] using g.le_opNorm y
  have ha := (abs_add_le (f x) (g y)).trans (add_le_add hf hg)
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr ha
  rw [sq_abs] at hs
  nlinarith [sq_nonneg (‖f‖ * ‖y‖ - ‖g‖ * ‖x‖)]

private lemma dual_cross_norm_sq_le (f : StrongDual ℝ E) (g : StrongDual ℝ F)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, (f x + g y) ^ 2 ≤ C * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    ‖f‖ ^ 2 + ‖g‖ ^ 2 ≤ C := by
  have hu (x : E) (y : F) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
      (f x) ^ 2 + (g y) ^ 2 ≤ C := by
    have hnx : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hny : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
    have hh := h ((f x) • x) ((g y) • y)
    simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hh
    have ht : C * ((f x) ^ 2 * ‖x‖ ^ 2 + (g y) ^ 2 * ‖y‖ ^ 2) ≤
        C * ((f x) ^ 2 + (g y) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [mul_one] using add_le_add
        (mul_le_mul_of_nonneg_left hnx (sq_nonneg (f x)))
        (mul_le_mul_of_nonneg_left hny (sq_nonneg (g y)))
    have hs : ((f x) ^ 2 + (g y) ^ 2) ^ 2 ≤ C * ((f x) ^ 2 + (g y) ^ 2) := by
      have hh' : ((f x) ^ 2 + (g y) ^ 2) ^ 2 ≤
          C * ((f x) ^ 2 * ‖x‖ ^ 2 + (g y) ^ 2 * ‖y‖ ^ 2) := by
        convert hh using 1 <;> ring
      exact hh'.trans ht
    have hn : 0 ≤ (f x) ^ 2 + (g y) ^ 2 := by positivity
    rcases eq_or_lt_of_le hn with hz | hp
    · simpa only [← hz] using hC
    · exact (mul_le_mul_iff_right₀ hp).mp (by simpa only [pow_two, mul_comm] using hs)
  have hf (y : F) (hy : ‖y‖ ≤ 1) : ‖f‖ ^ 2 + (g y) ^ 2 ≤ C := by
    have hn : 0 ≤ C - (g y) ^ 2 := by
      have hh := hu 0 y (by simp) hy
      simp only [map_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hh
      linarith
    have hh := dual_norm_sq_le_of_unit_sq f hn (fun x hx => by
      have hh := hu x y hx hy
      linarith)
    linarith
  have hn : 0 ≤ C - ‖f‖ ^ 2 := by
    have hh := hf 0 (by simp)
    simp only [map_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hh
    linarith
  have hh := dual_norm_sq_le_of_unit_sq g hn (fun y hy => by
    have hh := hf y hy
    linarith)
  linarith

/-- Inclusion of the head into the actual lp2 product. -/
def prodL2Inl (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : E →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E F)

/-- Inclusion of the tail into the actual lp2 product. -/
def prodL2Inr (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : F →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ E F)

@[simp] theorem prodL2Inl_apply (x : E) :
    prodL2Inl E F x = WithLp.toLp 2 (x, 0) := rfl

@[simp] theorem prodL2Inr_apply (y : F) :
    prodL2Inr E F y = WithLp.toLp 2 (0, y) := rfl

@[simp] theorem prodL2Inl_norm (x : E) : ‖prodL2Inl E F x‖ = ‖x‖ :=
  WithLp.norm_toLp_fst 2 E F x

@[simp] theorem prodL2Inr_norm (y : F) : ‖prodL2Inr E F y‖ = ‖y‖ :=
  WithLp.norm_toLp_snd 2 E F y

/-- Restriction of a product functional to its head. -/
def prodL2DualFst (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    StrongDual ℝ (WithLp 2 (E × F)) →L[ℝ] StrongDual ℝ E :=
  ContinuousLinearMap.precomp ℝ (prodL2Inl E F)

/-- Restriction of a product functional to its tail. -/
def prodL2DualSnd (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    StrongDual ℝ (WithLp 2 (E × F)) →L[ℝ] StrongDual ℝ F :=
  ContinuousLinearMap.precomp ℝ (prodL2Inr E F)

@[simp] theorem prodL2DualFst_apply (φ : StrongDual ℝ (WithLp 2 (E × F))) (x : E) :
    prodL2DualFst E F φ x = φ (WithLp.toLp 2 (x, 0)) := rfl

@[simp] theorem prodL2DualSnd_apply (φ : StrongDual ℝ (WithLp 2 (E × F))) (y : F) :
    prodL2DualSnd E F φ y = φ (WithLp.toLp 2 (0, y)) := rfl

theorem prodL2Dual_decompose (φ : StrongDual ℝ (WithLp 2 (E × F)))
    (z : WithLp 2 (E × F)) :
    φ z = prodL2DualFst E F φ z.ofLp.1 + prodL2DualSnd E F φ z.ofLp.2 := by
  have he : z = WithLp.toLp 2 (z.ofLp.1, (0 : F)) +
      WithLp.toLp 2 ((0 : E), z.ofLp.2) := by
    apply WithLp.ofLp_injective
    change z.ofLp = (z.ofLp.1, (0 : F)) + ((0 : E), z.ofLp.2)
    change z.ofLp = (z.ofLp.1 + 0, 0 + z.ofLp.2)
    rw [add_zero, zero_add]
  calc
    φ z = φ (WithLp.toLp 2 (z.ofLp.1, (0 : F)) +
        WithLp.toLp 2 ((0 : E), z.ofLp.2)) := congrArg φ he
    _ = _ := by rw [map_add]; rfl

/-- The exact lp2 dual norm, obtained from squared evaluations. -/
theorem prodL2Dual_norm_sq (φ : StrongDual ℝ (WithLp 2 (E × F))) :
    ‖φ‖ ^ 2 = ‖prodL2DualFst E F φ‖ ^ 2 + ‖prodL2DualSnd E F φ‖ ^ 2 := by
  apply le_antisymm
  · apply dual_norm_sq_le_of_unit_sq φ (by positivity)
    intro z hz
    rw [prodL2Dual_decompose]
    have h := dual_cross_eval_sq_le (prodL2DualFst E F φ) (prodL2DualSnd E F φ)
      z.ofLp.1 z.ofLp.2
    change (_ + _) ^ 2 ≤ (_ + _) * (‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2) at h
    rw [← WithLp.prod_norm_sq_eq_of_L2 z] at h
    have hz' : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    exact h.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hz' (by positivity :
        0 ≤ ‖prodL2DualFst E F φ‖ ^ 2 + ‖prodL2DualSnd E F φ‖ ^ 2))
  · apply dual_cross_norm_sq_le _ _ (sq_nonneg ‖φ‖)
    intro x y
    have he : prodL2DualFst E F φ x + prodL2DualSnd E F φ y =
        φ (WithLp.toLp 2 (x, y)) := by
      simpa only [WithLp.ofLp_toLp] using
        (prodL2Dual_decompose φ (WithLp.toLp 2 (x, y))).symm
    rw [he]
    have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (φ.le_opNorm (WithLp.toLp 2 (x, y)))
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow,
      WithLp.prod_norm_sq_eq_of_L2, WithLp.fst, WithLp.snd, WithLp.ofLp_toLp] using h

/-- The actual dual product identification is a linear isometry equivalence. -/
def prodL2DualEquiv (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    StrongDual ℝ (WithLp 2 (E × F)) ≃ₗᵢ[ℝ] WithLp 2 (StrongDual ℝ E × StrongDual ℝ F) where
  toFun φ := WithLp.toLp 2 (prodL2DualFst E F φ, prodL2DualSnd E F φ)
  invFun z := (z.fst.coprod z.snd).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap
  left_inv φ := by
    ext z
    exact (prodL2Dual_decompose φ z).symm
  right_inv z := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · ext x
      change z.fst x + z.snd 0 = z.ofLp.1 x
      rw [map_zero, add_zero]
      rfl
    · ext y
      change z.fst 0 + z.snd y = z.ofLp.2 y
      rw [map_zero, zero_add]
      rfl
  map_add' φ ψ := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> ext x <;> rfl
  map_smul' c φ := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> ext x <;> rfl
  norm_map' φ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact (prodL2Dual_norm_sq φ).symm

/-- Pullback by a linear isometry equivalence preserves the real dual norm. -/
def realDualIsometryEquiv (e : E ≃ₗᵢ[ℝ] F) : StrongDual ℝ E ≃ₗᵢ[ℝ] StrongDual ℝ F where
  toFun φ := φ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  invFun ψ := ψ.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  left_inv φ := by ext x; exact congrArg φ (e.symm_apply_apply x)
  right_inv ψ := by ext y; exact congrArg ψ (e.apply_symm_apply y)
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl
  norm_map' φ := by
    change ‖φ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ = ‖φ‖
    have h₁ : ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
      e.toLinearIsometry.norm_toContinuousLinearMap_le
    have h₂ : ‖e.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
      e.symm.toLinearIsometry.norm_toContinuousLinearMap_le
    apply le_antisymm
    · exact (φ.opNorm_comp_le _).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left h₂ (norm_nonneg φ))
    · have he : (φ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
          e.toContinuousLinearEquiv.toContinuousLinearMap = φ := by
        ext x
        exact congrArg φ (e.symm_apply_apply x)
      calc
        ‖φ‖ = ‖(φ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
            e.toContinuousLinearEquiv.toContinuousLinearMap‖ := congrArg norm he.symm
        _ ≤ ‖φ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ *
            ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ _ := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left h₁
              (norm_nonneg (φ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap))

/-- The actual bidual of a two-term lp2 sum, without assuming reflexivity. -/
def prodL2BidualEquiv (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    StrongDual ℝ (StrongDual ℝ (WithLp 2 (E × F))) ≃ₗᵢ[ℝ]
      WithLp 2 (StrongDual ℝ (StrongDual ℝ E) × StrongDual ℝ (StrongDual ℝ F)) :=
  (realDualIsometryEquiv (prodL2DualEquiv E F)).trans
    (prodL2DualEquiv (StrongDual ℝ E) (StrongDual ℝ F))

/-- Any finite dimensional source with an exact head/tail squared-norm
decomposition inherits the local Hilbert estimate. -/
theorem localHilbert_of_norm_sq_decomposition [FiniteDimensional ℝ E]
    {d : ℕ} {D : ℝ} (hD : 2 ≤ D) (hE : Module.finrank ℝ E ≤ d)
    (hF : HasHilbertNormWithin F D)
    (hG : ∀ (S : Submodule ℝ G) [FiniteDimensional ℝ S],
      Module.finrank ℝ S ≤ d → HasHilbertNormWithin S 2)
    (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hsq : ∀ x : E, ‖x‖ ^ 2 = ‖A x‖ ^ 2 + ‖B x‖ ^ 2) :
    HasHilbertNormWithin E D := by
  have hB : HasHilbertNormWithin ↥B.range D :=
    (hG B.range ((LinearMap.finrank_range_le B.toLinearMap).trans hE)).mono hD
  exact hasHilbertNormWithin_of_norm_sq_sum (by linarith) hF hB
    A.toLinearMap B.rangeRestrict.toLinearMap hsq

/-- Local Hilbert control for the actual dual of a head/tail lp2 product. -/
theorem localHilbert_prodL2_dual {d : ℕ} {D : ℝ} (hD : 2 ≤ D)
    (hE : HasHilbertNormWithin E D)
    (hF : ∀ (S : Submodule ℝ (StrongDual ℝ F)) [FiniteDimensional ℝ S],
      Module.finrank ℝ S ≤ d → HasHilbertNormWithin S 2)
    (S : Submodule ℝ (StrongDual ℝ (WithLp 2 (E × F)))) [FiniteDimensional ℝ S]
    (hS : Module.finrank ℝ S ≤ d) : HasHilbertNormWithin S D := by
  exact localHilbert_of_norm_sq_decomposition hD hS (hE.dual (by linarith)) hF
    ((prodL2DualFst E F).comp S.subtypeL) ((prodL2DualSnd E F).comp S.subtypeL)
    (fun φ => prodL2Dual_norm_sq (φ : StrongDual ℝ (WithLp 2 (E × F))))

theorem localHilbert_isometry_prodL2 {d : ℕ} {D : ℝ} (hD : 2 ≤ D)
    (e : E ≃ₗᵢ[ℝ] WithLp 2 (F × G)) (hF : HasHilbertNormWithin F D)
    (hG : LocallyHilbertWithin G d 2) : LocallyHilbertWithin E d D := by
  intro S _ hS
  let U := e.toContinuousLinearEquiv.toContinuousLinearMap.comp S.subtypeL
  let A := (WithLp.fstL 2 ℝ F G).comp U
  let B := (WithLp.sndL 2 ℝ F G).comp U
  apply localHilbert_of_norm_sq_decomposition hD hS hF hG A B
  intro x
  calc
    ‖x‖ ^ 2 = ‖e (x : E)‖ ^ 2 := by
      rw [e.norm_map]
      rfl
    _ = ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _

set_option maxHeartbeats 800000 in
/-- Local Hilbert control for the actual bidual of a head/tail lp2 product. -/
theorem localHilbert_prodL2_bidual {d : ℕ} {D : ℝ} (hD : 2 ≤ D)
    (hE : HasHilbertNormWithin E D)
    (hF : LocallyHilbertWithin (StrongDual ℝ (StrongDual ℝ F)) d 2) :
    LocallyHilbertWithin (StrongDual ℝ (StrongDual ℝ (WithLp 2 (E × F)))) d D := by
  exact localHilbert_isometry_prodL2
    (E := StrongDual ℝ (StrongDual ℝ (WithLp 2 (E × F))))
    (F := StrongDual ℝ (StrongDual ℝ E)) (G := StrongDual ℝ (StrongDual ℝ F))
    hD (prodL2BidualEquiv E F)
    (hE.bidual (by linarith)) hF

end ComplementedSubspace
