import ComplementedSubspace.FiniteOverlapUpper
import ComplementedSubspace.FiniteOverlapMatrixNorms

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace ComplementedSubspace

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Fully substituted finite overlap upper bound. Every matrix and moment
comes from the actual unconditional basis and the actual coordinate maps. -/
theorem finite_basis_overlap_bound (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {m : ℕ} (b : Module.Basis (Fin m) ℝ F) (T : F ≃L[ℝ] G)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (e : F →L[ℝ] FrameCoefficient n p) (h : F →L[ℝ] H)
    (C : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ z, ‖T z‖ ≤ ‖z‖) (hhi : ∀ z, ‖z‖ ≤ D * ‖T z‖)
    (hnormal : ∀ i, ‖T (b i)‖ = 1)
    (heH : ∀ z, ‖WithLp.toLp 2 (fun k => e z k)‖ ≤ ‖T z‖)
    (hP : ∀ x, ‖T (P x)‖ ≤ ‖x‖)
    (hnorm : ∀ z, ‖z‖ ^ 2 = ‖e z‖ ^ 2 + ‖h z‖ ^ 2)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1)
    (he : ∀ x, e (P (WithLp.toLp 2 x)) = R.mulVec x)
    (hh : ‖h.comp P‖ ≤ 1) :
    finiteAverage (fun x => ‖P (overlapInputRow n x)‖) ≤
      (C : ℝ) * (realFrameSignConstant p *
        (((C : ℝ) ^ 2 * ((3 : ℝ) ^ ((p - 2) / p) + 1)) ^ ((4 - p) / (2 * p)) *
          ((m : ℝ) * ((C : ℝ) * D) ^ 8 * (5 / 8 : ℝ) ^ n) ^ ((p - 2) / (2 * p))) +
        (C : ℝ) * Real.sqrt ((3 : ℝ) ^ ((p - 2) / p) + 1)) := by
  let B := finiteBasisFrameMatrix n p b e
  let V := finiteBasisAnalysisMatrix n b P
  have hB : ‖B‖ ≤ (C : ℝ) * D :=
    finiteBasisFrameMatrix_norm_le n p b T e C hb hD hlo hhi hnormal heH
  have hV : ‖V‖ ≤ (C : ℝ) * D :=
    finiteBasisAnalysisMatrix_norm_le n b T P C hb hD hlo hhi hnormal hP
  have hcoord (z : F) : (∑ k, (e z k) ^ 2) ≤ ‖T z‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (heH z) 2
    simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply] using hh
  have hsecond : finiteAverage (frameOverlapEnergy n B V) ≤
      (C : ℝ) ^ 2 * ((3 : ℝ) ^ ((p - 2) / p) + 1) :=
    finite_basis_frameOverlap_good_second n p hp₂ hp₄ b T.toLinearMap hlo P e h hnorm
      hcoord R hR he hh C hb
  have hroot := frameOverlapEnergy_moment_root_le_of_second n B V p hp₂ hp₄
    ((C : ℝ) ^ 2 * ((3 : ℝ) ^ ((p - 2) / p) + 1)) (by positivity) hsecond
  have hprod : (‖B‖ * ‖V‖) ^ 4 ≤ ((C : ℝ) * D) ^ 8 := by
    have hmul := mul_le_mul hB hV (norm_nonneg V) (mul_nonneg C.coe_nonneg hD)
    have hp := pow_le_pow_left₀ (mul_nonneg (norm_nonneg B) (norm_nonneg V)) hmul 4
    calc
      _ ≤ (((C : ℝ) * D) * ((C : ℝ) * D)) ^ 4 := hp
      _ = _ := by ring
  have hfourth : (Fintype.card (Fin m) : ℝ) * (‖B‖ * ‖V‖) ^ 4 * (5 / 8 : ℝ) ^ n ≤
      (m : ℝ) * ((C : ℝ) * D) ^ 8 * (5 / 8 : ℝ) ^ n := by
    simp only [Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)) (by positivity)
  have hroot' : (finiteAverage (fun tx => frameOverlapEnergy n B V tx ^ (p / 2))) ^ (1 / p) ≤
      ((C : ℝ) ^ 2 * ((3 : ℝ) ^ ((p - 2) / p) + 1)) ^ ((4 - p) / (2 * p)) *
        ((m : ℝ) * ((C : ℝ) * D) ^ 8 * (5 / 8 : ℝ) ^ n) ^ ((p - 2) / (2 * p)) := by
    apply hroot.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hfourth
        (div_nonneg (sub_nonneg.mpr hp₂) (by linarith)))
      (by positivity)
  have hu := finite_basis_overlap_mean_upper n p hp₂ hp₄ b P e h hnorm R hR he hh C hb
  apply hu.trans
  have hbeta : 0 ≤ realFrameSignConstant p := by unfold realFrameSignConstant; positivity
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hroot' hbeta) le_rfl)
    C.coe_nonneg

end ComplementedSubspace
