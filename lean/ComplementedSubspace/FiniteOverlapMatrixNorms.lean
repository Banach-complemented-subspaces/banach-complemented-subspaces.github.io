import ComplementedSubspace.FiniteOverlapBasisColumns
import ComplementedSubspace.UnconditionalHilbertSynthesis

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace ComplementedSubspace

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem finiteBasisFrameMatrix_mulVec (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    {m : ℕ} (b : Module.Basis (Fin m) ℝ F) (e : F →L[ℝ] FrameCoefficient n p)
    (a : Fin m → ℝ) :
    (finiteBasisFrameMatrix n p b e).mulVec a = e (b.equivFun.symm a) := by
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul]
  funext k
  let l : FrameCoefficient n p →ₗ[ℝ] ℝ :=
    { toFun := fun z => z k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change (finiteBasisFrameMatrix n p b e).mulVec a k = l (∑ i, a i • e (b i))
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ i, e (b i) k * a i) = (∑ i, a i * e (b i) k)
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finiteBasisAnalysisMatrix_transpose_mulVec (n : ℕ) {m : ℕ}
    (b : Module.Basis (Fin m) ℝ F) (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (x : MomentIndex n → ℝ) :
    (finiteBasisAnalysisMatrix n b P).transpose.mulVec x = b.equivFun (P (WithLp.toLp 2 x)) := by
  funext i
  change (∑ k, finiteBasisAnalysisFunctional n b P i (Pi.single k 1) * x k) =
    finiteBasisAnalysisFunctional n b P i x
  rw [linearMap_pi_eq_sum_single]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The concrete frame synthesis matrix inherits the actual normalized
unconditional-basis Hilbert estimate. -/
theorem finiteBasisFrameMatrix_norm_le (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    {m : ℕ} (b : Module.Basis (Fin m) ℝ F) (T : F ≃L[ℝ] G)
    (e : F →L[ℝ] FrameCoefficient n p)
    (C : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ z, ‖T z‖ ≤ ‖z‖) (hhi : ∀ z, ‖z‖ ≤ D * ‖T z‖)
    (hnormal : ∀ i, ‖T (b i)‖ = 1)
    (he : ∀ z, ‖WithLp.toLp 2 (fun k => e z k)‖ ≤ ‖T z‖) :
    ‖finiteBasisFrameMatrix n p b e‖ ≤ (C : ℝ) * D := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg C.coe_nonneg hD)
  intro a
  change ‖WithLp.toLp 2 ((finiteBasisFrameMatrix n p b e).mulVec (WithLp.ofLp a))‖ ≤ _
  have heq : WithLp.toLp 2 ((finiteBasisFrameMatrix n p b e).mulVec (WithLp.ofLp a)) =
      (WithLp.toLp 2 (fun k => e (b.equivFun.symm (WithLp.ofLp a)) k) : EuclideanSpace ℝ (MomentIndex n)) := by
    ext k
    exact congrFun (finiteBasisFrameMatrix_mulVec n p b e (WithLp.ofLp a)) k
  rw [heq]
  exact (he _).trans (unconditional_hilbert_synthesis_bounds b T C hb hD hlo hhi hnormal
    (WithLp.ofLp a)).1

/-- The concrete analysis columns inherit the inverse synthesis estimate
because the input map is a contraction in the coefficient Hilbert norm. -/
theorem finiteBasisAnalysisMatrix_norm_le (n : ℕ) {m : ℕ}
    (b : Module.Basis (Fin m) ℝ F) (T : F ≃L[ℝ] G)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (C : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ z, ‖T z‖ ≤ ‖z‖) (hhi : ∀ z, ‖z‖ ≤ D * ‖T z‖)
    (hnormal : ∀ i, ‖T (b i)‖ = 1)
    (hP : ∀ x, ‖T (P x)‖ ≤ ‖x‖) :
    ‖finiteBasisAnalysisMatrix n b P‖ ≤ (C : ℝ) * D := by
  rw [← real_opNorm_transpose, Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg C.coe_nonneg hD)
  intro x
  change ‖WithLp.toLp 2 ((finiteBasisAnalysisMatrix n b P).transpose.mulVec (WithLp.ofLp x))‖ ≤ _
  rw [finiteBasisAnalysisMatrix_transpose_mulVec]
  have h := (unconditional_hilbert_synthesis_bounds b T C hb hD hlo hhi hnormal
    (b.equivFun (P x))).2
  rw [b.equivFun.symm_apply_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hP x) (mul_nonneg C.coe_nonneg hD))

end ComplementedSubspace
