import ComplementedSubspace.FiniteOverlapBasisColumns
import ComplementedSubspace.FiniteOverlapRandomization
import ComplementedSubspace.DPRtoGL

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace ComplementedSubspace

def overlapInputRow (n : ℕ) (x : FrameIndex n) : EuclideanSpace ℝ (MomentIndex n) :=
  WithLp.toLp 2 (fun k => (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * realProductFrame n x k)

variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem basis_coordinate_overlapInputRow (n : ℕ) {m : ℕ}
    (b : Module.Basis (Fin m) ℝ F) (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (i : Fin m) (x : FrameIndex n) :
    b.coord i (P (overlapInputRow n x)) = (Real.sqrt ((2 : ℝ) ^ n))⁻¹ *
      productFrameEval n (fun k => finiteBasisAnalysisMatrix n b P k i) x := by
  change finiteBasisAnalysisFunctional n b P i
    (fun k => (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * realProductFrame n x k) = _
  rw [linearMap_pi_eq_sum_single]
  simp only [smul_eq_mul, productFrameEval, Finset.mul_sum, finiteBasisAnalysisMatrix]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem basis_randomized_frame_component (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (e : F →L[ℝ] FrameCoefficient n p) (x : FrameIndex n) (s : SignIndex m) :
    e (basisMultiplier b (realSignVector m s) (P (overlapInputRow n x))) =
      frameCoefficientRandomized n p (finiteBasisFrameMatrix n p b e)
        (finiteBasisAnalysisMatrix n b P) x s := by
  rw [basisMultiplier_sign_expansion, map_sum]
  simp only [map_smul]
  funext k
  let l : FrameCoefficient n p →ₗ[ℝ] ℝ :=
    { toFun := fun z => z k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change l (∑ i, (realSignVector m s i * b.coord i (P (overlapInputRow n x))) • e (b i)) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ i, (realSignVector m s i * b.coord i (P (overlapInputRow n x))) * e (b i) k) = _
  simp only [basis_coordinate_overlapInputRow, frameCoefficientRandomized,
    Finset.mul_sum, finiteBasisFrameMatrix]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem basis_randomized_row_hilbert_second (n : ℕ) {m : ℕ}
    (b : Module.Basis (Fin m) ℝ F) (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (h : F →L[ℝ] H) :
    finiteAverage (fun x => finiteAverage (fun s =>
      ‖h (basisMultiplier b (realSignVector m s) (P (overlapInputRow n x)))‖ ^ 2)) =
      ((2 : ℝ) ^ n)⁻¹ * ∑ i,
        (∑ k, finiteBasisAnalysisMatrix n b P k i ^ 2) * ‖h (b i)‖ ^ 2 := by
  have hpoint (x : FrameIndex n) :
      finiteAverage (fun s => ‖h (basisMultiplier b (realSignVector m s)
        (P (overlapInputRow n x)))‖ ^ 2) =
        ∑ i, (b.coord i (P (overlapInputRow n x))) ^ 2 * ‖h (b i)‖ ^ 2 :=
    finiteAverage_basisMultiplier_hilbert_sq b h.toLinearMap _
  simp only [hpoint, basis_coordinate_overlapInputRow, mul_pow]
  rw [finiteAverage_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteAverage_mul_right, finiteAverage_mul,
    productFrameEval_second_moment, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ) ^ n)]
  ring

theorem basis_randomized_hilbert_mean_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (e : F →L[ℝ] FrameCoefficient n p) (h : F →L[ℝ] H)
    (hnorm : ∀ z, ‖z‖ ^ 2 = ‖e z‖ ^ 2 + ‖h z‖ ^ 2)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1)
    (he : ∀ x, e (P (WithLp.toLp 2 x)) = R.mulVec x)
    (hh : ‖h.comp P‖ ≤ 1) (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) :
    finiteAverage (fun x => finiteAverage (fun s =>
      ‖h (basisMultiplier b (realSignVector m s) (P (overlapInputRow n x)))‖)) ≤
      (C : ℝ) * Real.sqrt ((3 : ℝ) ^ ((p - 2) / p) + 1) := by
  have hhc (z : F) : ‖h z‖ ≤ ‖z‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    nlinarith [hnorm z, sq_nonneg ‖e z‖]
  have hsecond := finite_basis_good_second_columns n p hp₂ hp₄ b h.toLinearMap hhc
    P e h hnorm R hR he hh C hb
  have hsecond' := (basis_randomized_row_hilbert_second n b P h).le.trans hsecond
  let f : FrameIndex n × SignIndex m → ℝ := fun xs =>
    ‖h (basisMultiplier b (realSignVector m xs.2) (P (overlapInputRow n xs.1)))‖
  have hj := finiteAverage_rpow_le f (fun _ => norm_nonneg _) (2 : ℝ) (by norm_num)
  simp only [Real.rpow_two, finiteAverage_prod] at hj
  apply le_of_sq_le_sq _ (by positivity)
  calc
    _ ≤ finiteAverage (fun x => finiteAverage (fun s =>
        ‖h (basisMultiplier b (realSignVector m s) (P (overlapInputRow n x)))‖ ^ 2)) := hj
    _ ≤ (C : ℝ) ^ 2 * ((3 : ℝ) ^ ((p - 2) / p) + 1) := hsecond'
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]

theorem basis_sign_multiplier_involutive {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (s : SignIndex m) (z : F) :
    basisMultiplier b (realSignVector m s) (basisMultiplier b (realSignVector m s) z) = z := by
  have h := basisMultiplier_comp b (realSignVector m s) (realSignVector m s)
  have hs : (fun i => realSignVector m s i * realSignVector m s i) = fun _ => (1 : ℝ) := by
    funext i
    simpa only [pow_two] using realSignVector_coordinate_sq m s i
  rw [hs, basisMultiplier_one] at h
  exact congrArg (fun T : F →L[ℝ] F => T z) h

/-- The entire unconditional randomization upper bound, retaining the actual
first coordinate map `e` and Hilbert component `h`. -/
theorem finite_basis_overlap_mean_upper (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {m : ℕ} (b : Module.Basis (Fin m) ℝ F)
    (P : EuclideanSpace ℝ (MomentIndex n) →L[ℝ] F)
    (e : F →L[ℝ] FrameCoefficient n p) (h : F →L[ℝ] H)
    (hnorm : ∀ z, ‖z‖ ^ 2 = ‖e z‖ ^ 2 + ‖h z‖ ^ 2)
    (R : Matrix (MomentIndex n) (MomentIndex n) ℝ) (hR : ‖R‖ ≤ 1)
    (he : ∀ x, e (P (WithLp.toLp 2 x)) = R.mulVec x)
    (hh : ‖h.comp P‖ ≤ 1) (C : ℝ≥0)
    (hb : unconditionalBasisConstant b ≤ (C : ℝ≥0∞)) :
    finiteAverage (fun x => ‖P (overlapInputRow n x)‖) ≤
      (C : ℝ) * (realFrameSignConstant p *
        (finiteAverage (fun tx => frameOverlapEnergy n (finiteBasisFrameMatrix n p b e)
          (finiteBasisAnalysisMatrix n b P) tx ^ (p / 2))) ^ (1 / p) +
        (C : ℝ) * Real.sqrt ((3 : ℝ) ^ ((p - 2) / p) + 1)) := by
  have hpoint (x : FrameIndex n) (s : SignIndex m) : ‖P (overlapInputRow n x)‖ ≤
      (C : ℝ) * (‖e (basisMultiplier b (realSignVector m s) (P (overlapInputRow n x)))‖ +
        ‖h (basisMultiplier b (realSignVector m s) (P (overlapInputRow n x)))‖) := by
    let z := basisMultiplier b (realSignVector m s) (P (overlapInputRow n x))
    have hM : ‖basisMultiplier b (realSignVector m s)‖ ≤ (C : ℝ) := by
      simpa only [mul_one] using norm_basisSignMultiplier_le b C hb s
        (fun _ => 1) (fun _ => by norm_num)
    have hz : ‖z‖ ≤ ‖e z‖ + ‖h z‖ := by
      apply le_of_sq_le_sq _ (by positivity)
      nlinarith [hnorm z, norm_nonneg (e z), norm_nonneg (h z)]
    calc
      _ = ‖basisMultiplier b (realSignVector m s) z‖ := by rw [basis_sign_multiplier_involutive]
      _ ≤ (C : ℝ) * ‖z‖ := (basisMultiplier b _).le_opNorm z |>.trans
        (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_left hz C.coe_nonneg
  have hupper : finiteAverage (fun x => ‖P (overlapInputRow n x)‖) ≤
      (C : ℝ) * (finiteAverage (fun x => finiteAverage (fun s =>
        ‖e (basisMultiplier b (realSignVector m s) (P (overlapInputRow n x)))‖)) +
      finiteAverage (fun x => finiteAverage (fun s =>
        ‖h (basisMultiplier b (realSignVector m s) (P (overlapInputRow n x)))‖))) := by
    calc
      _ = finiteAverage (fun x => finiteAverage (fun _ : SignIndex m => ‖P (overlapInputRow n x)‖)) := by
        simp only [finiteAverage_const]
      _ ≤ finiteAverage (fun x => finiteAverage (fun s =>
          (C : ℝ) * (‖e (basisMultiplier b (realSignVector m s) (P (overlapInputRow n x)))‖ +
            ‖h (basisMultiplier b (realSignVector m s) (P (overlapInputRow n x)))‖))) :=
        finiteAverage_mono _ _ fun x => finiteAverage_mono _ _ fun s => hpoint x s
      _ = _ := by simp only [finiteAverage_mul, finiteAverage_add]
  apply hupper.trans
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  apply add_le_add
  · simp only [basis_randomized_frame_component]
    exact frameCoefficientRandomized_mean_norm_le n p hp₂ hp₄ _ _
  · exact basis_randomized_hilbert_mean_le n p hp₂ hp₄ b P e h hnorm R hR he hh C hb

end ComplementedSubspace
