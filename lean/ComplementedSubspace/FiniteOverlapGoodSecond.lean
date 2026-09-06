import ComplementedSubspace.ProductFrameSignContraction
import ComplementedSubspace.FiniteBasisTraceBound
import ComplementedSubspace.FiniteHilbertAverage

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace ComplementedSubspace

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem basisMultiplier_sign_expansion {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (s : SignIndex m) (z : F) :
    basisMultiplier b (realSignVector m s) z =
      ∑ i, (realSignVector m s i * b.coord i z) • b i := by
  change b.constr ℝ (fun i => realSignVector m s i • b i) z = _
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.coord_apply, Module.Basis.equivFun_apply, smul_smul, mul_comm]

theorem finiteAverage_basisMultiplier_hilbert_sq {m : ℕ}
    (b : Module.Basis (Fin m) ℝ F) (L : F →ₗ[ℝ] G) (z : F) :
    finiteAverage (fun s => ‖L (basisMultiplier b (realSignVector m s) z)‖ ^ 2) =
      ∑ i, (b.coord i z) ^ 2 * ‖L (b i)‖ ^ 2 := by
  have hexp (s : SignIndex m) :
      ‖L (basisMultiplier b (realSignVector m s) z)‖ ^ 2 =
        ∑ i, ∑ j, realSignVector m s i * realSignVector m s j *
          ((b.coord i z * b.coord j z) * inner ℝ (L (b i)) (L (b j))) := by
    rw [basisMultiplier_sign_expansion, map_sum, ← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, map_smul, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm (L (b j)) (L (b i))]
    ring
  simp_rw [hexp]
  rw [finiteAverage_sign_bilinear]
  simp only [real_inner_self_eq_norm_sq, pow_two]

/-- Randomizing an actual unconditional basis controls its Hilbert-coordinate
energy whenever the coordinate Hilbert norm is below the Banach norm. -/
theorem finite_basis_hilbert_energy_le {m : ℕ}
    (b : Module.Basis (Fin m) ℝ F) (L : F →ₗ[ℝ] G)
    (hL : ∀ z, ‖L z‖ ≤ ‖z‖) (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) (z : F) :
    (∑ i, (b.coord i z) ^ 2 * ‖L (b i)‖ ^ 2) ≤ (C : ℝ) ^ 2 * ‖z‖ ^ 2 := by
  rw [← finiteAverage_basisMultiplier_hilbert_sq b L z]
  calc
    _ ≤ finiteAverage (fun _ : SignIndex m => (C : ℝ) ^ 2 * ‖z‖ ^ 2) := by
      apply finiteAverage_mono
      intro s
      have hM : ‖basisMultiplier b (realSignVector m s)‖ ≤ (C : ℝ) := by
        simpa only [mul_one] using norm_basisSignMultiplier_le b C hb s
          (fun _ => 1) (fun _ => by norm_num)
      have hN : ‖L (basisMultiplier b (realSignVector m s) z)‖ ≤ (C : ℝ) * ‖z‖ :=
        (hL _).trans ((basisMultiplier b _).le_opNorm z |>.trans
          (mul_le_mul_of_nonneg_right hM (norm_nonneg _)))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hN 2
    _ = _ := finiteAverage_const _

/-- The norm of the projected normalized signs has a uniform second moment,
provided its two actual components are Hilbert contractions before the frame
coefficient norm is imposed. -/
theorem finite_projection_sign_norm_sq_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (e : F →L[ℝ] FrameCoefficient n p) (h : F →L[ℝ] H)
    (hnorm : ∀ z, ‖z‖ ^ 2 = ‖e z‖ ^ 2 + ‖h z‖ ^ 2)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1)
    (he : ∀ x, e (P (WithLp.toLp 2 x)) = R.mulVec x)
    (hh : ‖h.comp P‖ ≤ 1) :
    finiteAverage (fun s => ‖P (WithLp.toLp 2 (normalizedFrameSign n s))‖ ^ 2) ≤
      (3 : ℝ) ^ ((p - 2) / p) + 1 := by
  simp_rw [hnorm, finiteAverage_add]
  have hE : finiteAverage (fun s => ‖e (P (WithLp.toLp 2 (normalizedFrameSign n s)))‖ ^ 2) ≤
      (3 : ℝ) ^ ((p - 2) / p) := by
    simp only [he]
    exact frameCoefficientContractedSign_norm_sq_average_le n p hp₂ hp₄ R hR
  have hH : finiteAverage (fun s => ‖h (P (WithLp.toLp 2 (normalizedFrameSign n s)))‖ ^ 2) ≤ 1 := by
    calc
      _ ≤ finiteAverage (fun _ : SignIndex (Fintype.card (MomentIndex n)) => (1 : ℝ)) := by
        apply finiteAverage_mono
        intro s
        have hx : ‖WithLp.toLp 2 (normalizedFrameSign n s)‖ ^ 2 = 1 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          exact normalizedFrameSign_length_sq n s
        have hb := (h.comp P).le_opNorm (WithLp.toLp 2 (normalizedFrameSign n s))
        have hle : ‖h (P (WithLp.toLp 2 (normalizedFrameSign n s)))‖ ≤
            ‖WithLp.toLp 2 (normalizedFrameSign n s)‖ := by
          exact hb.trans ((mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _))
        simpa only [hx] using pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = 1 := finiteAverage_const _
  exact add_le_add hE hH

/-- The good second moment needed in the overlap proof. The constant has no
factor from the upper coefficient-to-Hilbert comparison. -/
theorem finite_basis_good_second_moment (n : ℕ) (p : ℝ)
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
    finiteAverage (fun s => ∑ i,
      (b.coord i (P (WithLp.toLp 2 (normalizedFrameSign n s)))) ^ 2 * ‖L (b i)‖ ^ 2) ≤
      (C : ℝ) ^ 2 * ((3 : ℝ) ^ ((p - 2) / p) + 1) := by
  calc
    _ ≤ finiteAverage (fun s => (C : ℝ) ^ 2 *
        ‖P (WithLp.toLp 2 (normalizedFrameSign n s))‖ ^ 2) :=
      finiteAverage_mono _ _ fun s => finite_basis_hilbert_energy_le b L hL C hb _
    _ = (C : ℝ) ^ 2 * finiteAverage
        (fun s => ‖P (WithLp.toLp 2 (normalizedFrameSign n s))‖ ^ 2) := finiteAverage_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (finite_projection_sign_norm_sq_le n p hp₂ hp₄ P e h hnorm R hR he hh) (sq_nonneg _)

end ComplementedSubspace
