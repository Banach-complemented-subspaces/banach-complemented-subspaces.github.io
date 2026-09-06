import ComplementedSubspace.ProductFrameTrace
import ComplementedSubspace.ProductFrameWitness
import ComplementedSubspace.ProductFrameSignSample

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace ComplementedSubspace

def finiteVectorAverage {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (f : ι → E) : E := (Fintype.card ι : ℝ)⁻¹ • ∑ i, f i

theorem finiteVectorAverage_norm_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ι → E) :
    ‖finiteVectorAverage f‖ ≤ finiteAverage (fun i => ‖f i‖) := by
  unfold finiteVectorAverage finiteAverage
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

theorem frameSymmetry_twirl (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 0 < p) (T : FrameCoefficient n p →ₗ[ℝ] FrameCoefficient n p)
    (x : FrameCoefficient n p) :
    finiteVectorAverage (fun u =>
      (frameSymmetryEquiv n p hp u).symm (T (frameSymmetryEquiv n p hp u x))) =
      (((2 : ℝ) ^ n)⁻¹ * LinearMap.trace ℝ (FrameCoefficient n p) T) • x := by
  funext i
  change (Fintype.card (FrameIndex n) : ℝ)⁻¹ *
    (∑ u, (frameSymmetryEquiv n p hp u).symm (T (frameSymmetryEquiv n p hp u x))) i = _
  rw [Finset.sum_apply]
  exact frameSymmetry_twirl_coordinate n p hp T x i

/-- A finite trace estimate from a verified symmetry-orbit second moment. -/
theorem frame_trace_bound_of_orbit_moment (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : FrameCoefficient n p →L[ℝ] H) (B : H →L[ℝ] FrameCoefficient n p)
    (x : FrameCoefficient n p) (a : ℝ) (ha : 0 ≤ a)
    (hmoment : finiteAverage (fun u => ‖A (frameSymmetryEquiv n p hp u x)‖ ^ 2) ≤
      a ^ 2 * ‖A‖ ^ 2) :
    |LinearMap.trace ℝ (FrameCoefficient n p) (B.comp A).toLinearMap| * ‖x‖ ≤
      (2 : ℝ) ^ n * a * ‖A‖ * ‖B‖ := by
  let f : FrameIndex n → ℝ := fun u => ‖A (frameSymmetryEquiv n p hp u x)‖
  have hJ := finiteAverage_rpow_le f (fun _ => norm_nonneg _) (2 : ℝ) (by norm_num)
  simp_rw [Real.rpow_two] at hJ
  have hmean : finiteAverage f ≤ a * ‖A‖ := by
    apply le_of_sq_le_sq _ (by positivity)
    calc
      _ ≤ finiteAverage (fun u => f u ^ 2) := hJ
      _ ≤ a ^ 2 * ‖A‖ ^ 2 := hmoment
      _ = _ := by ring
  let v : FrameIndex n → FrameCoefficient n p := fun u =>
    (frameSymmetryEquiv n p hp u).symm (B (A (frameSymmetryEquiv n p hp u x)))
  have hv : finiteVectorAverage v =
      (((2 : ℝ) ^ n)⁻¹ * LinearMap.trace ℝ (FrameCoefficient n p)
        (B.comp A).toLinearMap) • x :=
    frameSymmetry_twirl n p hp (B.comp A).toLinearMap x
  have hb : ‖finiteVectorAverage v‖ ≤ ‖B‖ * (a * ‖A‖) := by
    calc
      _ ≤ finiteAverage (fun u => ‖v u‖) := finiteVectorAverage_norm_le v
      _ ≤ finiteAverage (fun u => ‖B‖ * f u) := by
        apply finiteAverage_mono
        intro u
        change ‖(frameSymmetryEquiv n p hp u).symm
          (B (A (frameSymmetryEquiv n p hp u x)))‖ ≤
            ‖B‖ * ‖A (frameSymmetryEquiv n p hp u x)‖
        rw [LinearIsometryEquiv.norm_map]
        exact B.le_opNorm _
      _ = ‖B‖ * finiteAverage f := finiteAverage_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean (norm_nonneg _)
  rw [hv, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ((2 : ℝ) ^ n)⁻¹)] at hb
  have hq : (2 : ℝ) ^ n ≠ 0 := by positivity
  calc
    _ = (2 : ℝ) ^ n *
        ((((2 : ℝ) ^ n)⁻¹ *
          |LinearMap.trace ℝ (FrameCoefficient n p) (B.comp A).toLinearMap|) * ‖x‖) := by
      field_simp
    _ ≤ (2 : ℝ) ^ n * (‖B‖ * (a * ‖A‖)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

def realFrameSignConstant (p : ℝ) : ℝ := (3 : ℝ) ^ ((p - 2) / (2 * p))

theorem realFrameSignConstant_sq (p : ℝ) :
    realFrameSignConstant p ^ 2 = (3 : ℝ) ^ ((p - 2) / p) := by
  rw [realFrameSignConstant, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  norm_num
  ring

theorem frameSymmetry_hilbert_orbit_moment (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : FrameCoefficient n p →L[ℝ] H) :
    finiteAverage (fun u =>
      ‖A (frameSymmetryEquiv n p (by linarith) u (frameCoefficientWitness n p))‖ ^ 2) ≤
      realFrameSignConstant p ^ 2 * ‖A‖ ^ 2 := by
  let L : (MomentIndex n → ℝ) →ₗ[ℝ] H :=
    { toFun := fun b => A b
      map_add' := A.map_add
      map_smul' := A.map_smul }
  have hcov (i j : MomentIndex n) :
      finiteAverage (fun u => frameSymmetry n u (frameWitness n) i *
        frameSymmetry n u (frameWitness n) j) =
      finiteAverage (fun s => normalizedFrameSign n s i * normalizedFrameSign n s j) := by
    rw [frameSymmetry_covariance, normalizedFrameSign_covariance]
    simp only [← pow_two, frameWitness_euclidean_sq, mul_one]
    split_ifs <;> simp
  have hreplace := finiteAverage_linearMap_norm_sq_eq_of_covariance
    (fun u => frameSymmetry n u (frameWitness n)) (normalizedFrameSign n) hcov L
  change finiteAverage (fun u => ‖L (frameSymmetry n u (frameWitness n))‖ ^ 2) ≤ _
  rw [hreplace]
  change finiteAverage (fun s => ‖A (frameCoefficientSignSample n p s)‖ ^ 2) ≤ _
  calc
    _ ≤ finiteAverage (fun s => ‖A‖ ^ 2 * ‖frameCoefficientSignSample n p s‖ ^ 2) := by
      apply finiteAverage_mono
      intro s
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (A.le_opNorm (frameCoefficientSignSample n p s)) 2
    _ = ‖A‖ ^ 2 * finiteAverage (fun s => ‖frameCoefficientSignSample n p s‖ ^ 2) :=
      finiteAverage_mul _ _
    _ ≤ ‖A‖ ^ 2 * (3 : ℝ) ^ ((p - 2) / p) :=
      mul_le_mul_of_nonneg_left
        (frameCoefficientSignSample_norm_sq_average_le n p hp₂ hp₄) (sq_nonneg _)
    _ = _ := by rw [realFrameSignConstant_sq]; ring

/-- The direct finite-frame Hilbert-factorization trace inequality. All orbit,
sign-moment and witness constants are proved for the actual normed space. -/
theorem realFrame_hilbert_trace_bound_mul (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : FrameCoefficient n p →L[ℝ] H) (B : H →L[ℝ] FrameCoefficient n p) :
    |LinearMap.trace ℝ (FrameCoefficient n p) (B.comp A).toLinearMap| *
        realFrameWitnessScale n p ≤
      (2 : ℝ) ^ n * realFrameSignConstant p * ‖A‖ * ‖B‖ := by
  have h := frame_trace_bound_of_orbit_moment n p (by linarith) A B
    (frameCoefficientWitness n p) (realFrameSignConstant p)
    (Real.rpow_nonneg (by norm_num) _)
    (frameSymmetry_hilbert_orbit_moment n p hp₂ hp₄ A)
  simpa only [frameCoefficientWitness_norm n p (by linarith)] using h

theorem realFrame_hilbert_trace_bound (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : FrameCoefficient n p →L[ℝ] H) (B : H →L[ℝ] FrameCoefficient n p) :
    |LinearMap.trace ℝ (FrameCoefficient n p) (B.comp A).toLinearMap| ≤
      ((2 : ℝ) ^ n * realFrameSignConstant p / realFrameWitnessScale n p) * ‖A‖ * ‖B‖ := by
  have hg : 0 < realFrameWitnessScale n p := Real.exp_pos _
  have h := realFrame_hilbert_trace_bound_mul n p hp₂ hp₄ A B
  calc
    _ ≤ ((2 : ℝ) ^ n * realFrameSignConstant p * ‖A‖ * ‖B‖) /
        realFrameWitnessScale n p := (le_div_iff₀ hg).mpr h
    _ = _ := by ring

end ComplementedSubspace
