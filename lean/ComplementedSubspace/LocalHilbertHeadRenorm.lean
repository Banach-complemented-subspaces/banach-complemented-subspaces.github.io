import ComplementedSubspace.LocalHilbertQuotient

/-!
# Global Hilbert renorming of the head before a quotient operation

The tail norm is unchanged. The head is replaced by an actual Hilbert norm,
so the global product inherits the tail's approximate parallelogram constant.
The resulting dual-subspace-dual estimate incurs only the global head
distortion times the freely chosen local Hilbert distortion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ApproxParallelogram.prodL2 {ν : ℝ}
    (hE : ApproxParallelogram (fun x : E => ‖x‖) ν)
    (hF : ApproxParallelogram (fun x : F => ‖x‖) ν) :
    ApproxParallelogram (fun x : WithLp 2 (E × F) => ‖x‖) ν := by
  intro x y
  have hx := hE x.fst y.fst
  have hy := hF x.snd y.snd
  dsimp only at hx hy ⊢
  simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.add_fst, WithLp.add_snd,
    WithLp.sub_fst, WithLp.sub_snd]
  nlinarith

def headTailRenormLinear (p : HilbertNormModel E) :
    WithLp 2 (E × F) ≃ₗ[ℝ] WithLp 2 (p.Space × F) :=
  ((show E ≃ₗ[ℝ] p.Space from LinearEquiv.refl ℝ E).prodCongr
    (LinearEquiv.refl ℝ F)).withLpCongr 2

theorem headTailRenormLinear_bounds (p : HilbertNormModel E) {D : ℝ} (hD : 1 ≤ D)
    (hp : ∀ x : E, p.q x ≤ ‖x‖ ∧ ‖x‖ ≤ D * p.q x) (z : WithLp 2 (E × F)) :
    ‖headTailRenormLinear (F := F) p z‖ ≤ ‖z‖ ∧
      ‖z‖ ≤ D * ‖headTailRenormLinear (F := F) p z‖ := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hp0 : 0 ≤ p.q z.fst := apply_nonneg p.q _
  have hsq : ‖headTailRenormLinear (F := F) p z‖ ^ 2 =
      p.q z.fst ^ 2 + ‖z.snd‖ ^ 2 := by
    exact WithLp.prod_norm_sq_eq_of_L2 _
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hsq, WithLp.prod_norm_sq_eq_of_L2]
    exact add_le_add ((sq_le_sq₀ hp0 (norm_nonneg _)).mpr (hp z.fst).1) le_rfl
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD0 (norm_nonneg _))).mp
    rw [mul_pow, hsq, WithLp.prod_norm_sq_eq_of_L2]
    have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD0 hp0)).mpr (hp z.fst).2
    have ht := (sq_le_sq₀ (norm_nonneg z.snd) (mul_nonneg hD0 (norm_nonneg z.snd))).mpr
      (le_mul_of_one_le_left (norm_nonneg z.snd) hD)
    nlinarith

def headTailRenormEquiv (p : HilbertNormModel E) {D : ℝ} (hD : 1 ≤ D)
    (hp : ∀ x : E, p.q x ≤ ‖x‖ ∧ ‖x‖ ≤ D * p.q x) :
    WithLp 2 (E × F) ≃L[ℝ] WithLp 2 (p.Space × F) :=
  LinearEquiv.toContinuousLinearEquivOfBounds (headTailRenormLinear p) 1 D
    (fun z => by simpa only [one_mul] using (headTailRenormLinear_bounds p hD hp z).1)
    (fun z => (headTailRenormLinear_bounds p hD hp z).2)

theorem headTailRenormEquiv_norm_le (p : HilbertNormModel E) {D : ℝ} (hD : 1 ≤ D)
    (hp : ∀ x : E, p.q x ≤ ‖x‖ ∧ ‖x‖ ≤ D * p.q x) :
    ‖(headTailRenormEquiv (F := F) p hD hp).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖headTailRenormLinear (F := F) p z‖ ≤ 1 * ‖z‖
  simpa only [one_mul] using (headTailRenormLinear_bounds p hD hp z).1

theorem headTailRenormEquiv_symm_norm_le (p : HilbertNormModel E) {D : ℝ} (hD : 1 ≤ D)
    (hp : ∀ x : E, p.q x ≤ ‖x‖ ∧ ‖x‖ ≤ D * p.q x) :
    ‖(headTailRenormEquiv (F := F) p hD hp).symm.toContinuousLinearMap‖ ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hD)
  intro z
  let e := headTailRenormEquiv (F := F) p hD hp
  change ‖e.symm z‖ ≤ D * ‖z‖
  have h := (headTailRenormLinear_bounds p hD hp (e.symm z)).2
  change ‖e.symm z‖ ≤ D * ‖e (e.symm z)‖ at h
  simpa only [e.apply_symm_apply] using h

/-- Uniform control on small subspaces of `V*`, for every `V ⊆ (head ⊕₂ tail)*`.
The original V is allowed to have arbitrarily large finite dimension or to
be infinite dimensional. -/
theorem exists_headTail_dual_subspace_dual_threshold (d : ℕ) {η : ℝ} (hη : 1 < η) :
    ∃ ν > 1, ∀ (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F],
      ∀ {D : ℝ}, 1 ≤ D → HasHilbertNormWithin E D →
      ApproxParallelogram (fun x : F => ‖x‖) ν →
      DualSubspacesLocallyHilbertWithin (StrongDual ℝ (WithLp 2 (E × F))) d (D * η) := by
  obtain ⟨ν, hν, hgood⟩ := exists_renorm_dual_subspace_dual_threshold d hη
  refine ⟨ν, hν, ?_⟩
  intro E F _ _ _ _ D hD hE hF V
  obtain ⟨p, hp⟩ := hE.exists_model
  have hhead : ApproxParallelogram (fun x : p.Space => ‖x‖) 1 := by
    intro x y
    simpa only [mul_one] using (parallelogram_law_with_norm ℝ x y).le
  have hpar : ApproxParallelogram (fun x : WithLp 2 (p.Space × F) => ‖x‖) ν :=
    (hhead.mono hν.le).prodL2 hF
  exact hgood (WithLp 2 (E × F)) (WithLp 2 (p.Space × F)) (zero_le_one.trans hD)
    (headTailRenormEquiv p hD hp) (headTailRenormEquiv_norm_le p hD hp)
    (headTailRenormEquiv_symm_norm_le p hD hp) hpar V

/-- The recursion-compatible form, using its already selected threshold ν. -/
theorem headTail_dual_subspace_dual_localHilbert {D ν η : ℝ} {d : ℕ}
    (hD : 1 ≤ D) (hν : 1 ≤ ν)
    (hgood : ∀ (G : Type (max u v)) [NormedAddCommGroup G] [NormedSpace ℝ G],
      ApproxParallelogram (fun x : G => ‖x‖) ν → LocallyHilbertWithin G d η)
    (hE : HasHilbertNormWithin E D)
    (hF : ApproxParallelogram (fun x : F => ‖x‖) ν) :
    DualSubspacesLocallyHilbertWithin (StrongDual ℝ (WithLp 2 (E × F))) d (D * η) := by
  obtain ⟨p, hp⟩ := hE.exists_model
  have hhead : ApproxParallelogram (fun x : p.Space => ‖x‖) 1 := by
    intro x y
    simpa only [mul_one] using (parallelogram_law_with_norm ℝ x y).le
  have hpar : ApproxParallelogram (fun x : WithLp 2 (p.Space × F) => ‖x‖) ν :=
    (hhead.mono hν).prodL2 hF
  exact renorm_dual_subspace_dual_localHilbert (zero_le_one.trans hD) hgood
    (headTailRenormEquiv p hD hp) (headTailRenormEquiv_norm_le p hD hp)
    (headTailRenormEquiv_symm_norm_le p hD hp) hpar

end ComplementedSubspace
