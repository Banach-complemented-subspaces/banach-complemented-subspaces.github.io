import ComplementedSubspace.FiniteOverlapBound
import ComplementedSubspace.FiniteOverlapScale

/-! The concrete finite-basis mean estimate with all scalar constants simplified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace ComplementedSubspace

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Actual finite-basis overlap mean, multiplied by the conjugate row-witness
norm. The only dimension restriction is the proved selection size bound. -/
theorem finite_basis_overlap_scaled_bound (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    {m : ℕ} (b : Module.Basis (Fin m) ℝ F) (T : F ≃L[ℝ] G)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (e : F →L[ℝ] FrameCoefficient n p) (h : F →L[ℝ] H)
    (C : ℝ≥0) (hC : 1 ≤ (C : ℝ))
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞))
    (hm : (m : ℝ) ≤ 3 * (2 : ℝ) ^ n)
    (hlo : ∀ z, ‖T z‖ ≤ ‖z‖)
    (hhi : ∀ z, ‖z‖ ≤ realFrameHilbertScale n p * ‖T z‖)
    (hnormal : ∀ i, ‖T (b i)‖ = 1)
    (heH : ∀ z, ‖WithLp.toLp 2 (fun k => e z k)‖ ≤ ‖T z‖)
    (hP : ∀ x, ‖T (P x)‖ ≤ ‖x‖)
    (hnorm : ∀ z, ‖z‖ ^ 2 = ‖e z‖ ^ 2 + ‖h z‖ ^ 2)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1)
    (he : ∀ x, e (P (WithLp.toLp 2 x)) = R.mulVec x)
    (hh : ‖h.comp P‖ ≤ 1) :
    realFrameWitnessScale n (frameConjugate p) *
      finiteAverage (fun x => ‖P (overlapInputRow n x)‖) ≤
      64 * (C : ℝ) ^ 3 / realFrameOverlapScale n p := by
  have hupper := finite_basis_overlap_bound n p hp₂ (by linarith) b T P e h C hb
    (show 0 ≤ realFrameHilbertScale n p from (Real.exp_pos _).le)
    hlo hhi hnormal heH hP hnorm R hR he hh
  exact (mul_le_mul_of_nonneg_left hupper (Real.exp_pos _).le).trans
    (finite_overlap_scale_bound n p m (C : ℝ) hp₂ hp₃ hC hm)

end ComplementedSubspace
