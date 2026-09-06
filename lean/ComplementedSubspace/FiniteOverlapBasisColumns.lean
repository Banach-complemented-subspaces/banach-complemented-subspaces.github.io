import ComplementedSubspace.FiniteOverlapGoodSecond
import ComplementedSubspace.FiniteOverlapMoments

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace ComplementedSubspace

theorem normalizedFrameSign_linear_second_moment (n : ℕ)
    (A : (MomentIndex n → ℝ) →ₗ[ℝ] ℝ) :
    finiteAverage (fun s => A (normalizedFrameSign n s) ^ 2) =
      ((2 : ℝ) ^ n)⁻¹ * ∑ k, A (Pi.single k 1) ^ 2 := by
  have h := finiteAverage_linearMap_norm_sq (normalizedFrameSign n) A
  simp only [Real.norm_eq_abs, sq_abs, normalizedFrameSign_covariance,
    ite_div, zero_div, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, real_inner_self_eq_norm_sq] at h
  simp only [Real.norm_eq_abs, sq_abs, one_div, ← Finset.sum_mul] at h
  simpa only [mul_comm] using h

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def finiteBasisAnalysisFunctional (n : ℕ) {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F) (i : Fin m) :
    (MomentIndex n → ℝ) →ₗ[ℝ] ℝ :=
  (b.coord i).comp (P.toLinearMap.comp (WithLp.linearEquiv 2 ℝ (MomentIndex n → ℝ)).symm.toLinearMap)

def finiteBasisAnalysisMatrix (n : ℕ) {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F) :
    Matrix (MomentIndex n) (Fin m) ℝ := fun k i => finiteBasisAnalysisFunctional n b P i (Pi.single k 1)

def finiteBasisFrameMatrix (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    {m : ℕ} (b : Module.Basis (Fin m) ℝ F) (e : F →L[ℝ] FrameCoefficient n p) :
    Matrix (MomentIndex n) (Fin m) ℝ := fun k i => e (b i) k

theorem finite_basis_sign_energy_eq_columns (n : ℕ) {m : ℕ}
    (b : Module.Basis (Fin m) ℝ F) (L : F →ₗ[ℝ] G)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F) :
    finiteAverage (fun s => ∑ i,
      (b.coord i (P (WithLp.toLp 2 (normalizedFrameSign n s)))) ^ 2 * ‖L (b i)‖ ^ 2) =
      ((2 : ℝ) ^ n)⁻¹ * ∑ i,
        (∑ k, finiteBasisAnalysisMatrix n b P k i ^ 2) * ‖L (b i)‖ ^ 2 := by
  rw [finiteAverage_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteAverage_mul_right]
  change finiteAverage (fun s => finiteBasisAnalysisFunctional n b P i
      (normalizedFrameSign n s) ^ 2) * ‖L (b i)‖ ^ 2 = _
  rw [normalizedFrameSign_linear_second_moment]
  change (((2 : ℝ) ^ n)⁻¹ * ∑ k, finiteBasisAnalysisMatrix n b P k i ^ 2) *
    ‖L (b i)‖ ^ 2 = _
  ring

theorem finite_basis_good_second_columns (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (L : F →ₗ[ℝ] G) (hL : ∀ z, ‖L z‖ ≤ ‖z‖)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (e : F →L[ℝ] FrameCoefficient n p) (h : F →L[ℝ] H)
    (hnorm : ∀ z, ‖z‖ ^ 2 = ‖e z‖ ^ 2 + ‖h z‖ ^ 2)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1)
    (he : ∀ x, e (P (WithLp.toLp 2 x)) = R.mulVec x)
    (hh : ‖h.comp P‖ ≤ 1) (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ i,
        (∑ k, finiteBasisAnalysisMatrix n b P k i ^ 2) * ‖L (b i)‖ ^ 2 ≤
      (C : ℝ) ^ 2 * ((3 : ℝ) ^ ((p - 2) / p) + 1) := by
  rw [← finite_basis_sign_energy_eq_columns n b L P]
  exact finite_basis_good_second_moment n p hp₂ hp₄ b L hL P e h hnorm R hR he hh C hb

/-- Concrete frame energy inherits the good second moment from the actual
unconditional basis and its coefficient Hilbert embedding. -/
theorem finite_basis_frameOverlap_good_second (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (L : F →ₗ[ℝ] G) (hL : ∀ z, ‖L z‖ ≤ ‖z‖)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (e : F →L[ℝ] FrameCoefficient n p) (h : F →L[ℝ] H)
    (hnorm : ∀ z, ‖z‖ ^ 2 = ‖e z‖ ^ 2 + ‖h z‖ ^ 2)
    (hcoord : ∀ z, (∑ k, (e z k) ^ 2) ≤ ‖L z‖ ^ 2)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1)
    (he : ∀ x, e (P (WithLp.toLp 2 x)) = R.mulVec x)
    (hh : ‖h.comp P‖ ≤ 1) (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) :
    finiteAverage (frameOverlapEnergy n (finiteBasisFrameMatrix n p b e)
      (finiteBasisAnalysisMatrix n b P)) ≤
      (C : ℝ) ^ 2 * ((3 : ℝ) ^ ((p - 2) / p) + 1) := by
  rw [frameOverlapEnergy_average]
  apply le_trans _ (finite_basis_good_second_columns n p hp₂ hp₄ b L hL P e h hnorm R hR he hh C hb)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  change (∑ k, (e (b i) k) ^ 2) * (∑ k, finiteBasisAnalysisMatrix n b P k i ^ 2) ≤ _
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (hcoord (b i)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end ComplementedSubspace
