import ComplementedSubspace.FrameCoefficientNorm
import ComplementedSubspace.ComplexFrameProjection

/-! The complex product-frame coefficient space, with its actual normalized
finite Lp norm. The underlying real scalar action is retained explicitly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal BigOperators
namespace ComplementedSubspace

def complexProductFrameEval (n : ℕ) (b : MomentIndex n → ℂ) (s : FrameIndex n) : ℂ :=
  ∑ i, b i * (realProductFrame n s i : ℂ)

@[simp] theorem complexProductFrameEval_re (n : ℕ) (b : MomentIndex n → ℂ) (s : FrameIndex n) :
    (complexProductFrameEval n b s).re = productFrameEval n (fun i => (b i).re) s := by
  simp [complexProductFrameEval, productFrameEval, Complex.mul_re]

@[simp] theorem complexProductFrameEval_im (n : ℕ) (b : MomentIndex n → ℂ) (s : FrameIndex n) :
    (complexProductFrameEval n b s).im = productFrameEval n (fun i => (b i).im) s := by
  simp [complexProductFrameEval, productFrameEval, Complex.mul_im]

theorem complexProductFrameEval_injective (n : ℕ) : Function.Injective (complexProductFrameEval n) := by
  intro b c h
  have hr : (fun i => (b i).re) = (fun i => (c i).re) := by
    apply productFrameEval_injective n
    funext s
    simpa using congrArg Complex.re (congrFun h s)
  have hi : (fun i => (b i).im) = (fun i => (c i).im) := by
    apply productFrameEval_injective n
    funext s
    simpa using congrArg Complex.im (congrFun h s)
  funext i
  exact Complex.ext (congrFun hr i) (congrFun hi i)

def ComplexFrameCoefficient (n : ℕ) (p : ℝ) := MomentIndex n → ℂ

instance (n : ℕ) (p : ℝ) : AddCommGroup (ComplexFrameCoefficient n p) :=
  inferInstanceAs (AddCommGroup (MomentIndex n → ℂ))
instance (n : ℕ) (p : ℝ) : Module ℂ (ComplexFrameCoefficient n p) :=
  inferInstanceAs (Module ℂ (MomentIndex n → ℂ))
instance (n : ℕ) (p : ℝ) : Module ℝ (ComplexFrameCoefficient n p) :=
  inferInstanceAs (Module ℝ (MomentIndex n → ℂ))
instance (n : ℕ) (p : ℝ) : IsScalarTower ℝ ℂ (ComplexFrameCoefficient n p) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (MomentIndex n → ℂ))
instance (n : ℕ) (p : ℝ) : FiniteDimensional ℂ (ComplexFrameCoefficient n p) :=
  inferInstanceAs (FiniteDimensional ℂ (MomentIndex n → ℂ))
instance (n : ℕ) (p : ℝ) : FiniteDimensional ℝ (ComplexFrameCoefficient n p) :=
  inferInstanceAs (FiniteDimensional ℝ (MomentIndex n → ℂ))

def complexFrameCoefficientEmbedding (n : ℕ) (p : ℝ) :
    ComplexFrameCoefficient n p →ₗ[ℂ] PiLp (ENNReal.ofReal p) (fun _ : FrameIndex n => ℂ) where
  toFun b := WithLp.toLp (ENNReal.ofReal p)
    (fun s => (frameNormalization n p : ℂ) * complexProductFrameEval n b s)
  map_add' b c := by
    ext s
    change (frameNormalization n p : ℂ) * (∑ i, (b i + c i) * (realProductFrame n s i : ℂ)) =
      (frameNormalization n p : ℂ) * (∑ i, b i * (realProductFrame n s i : ℂ)) +
      (frameNormalization n p : ℂ) * (∑ i, c i * (realProductFrame n s i : ℂ))
    simp [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c b := by
    ext s
    change (frameNormalization n p : ℂ) * (∑ i, (c * b i) * (realProductFrame n s i : ℂ)) =
      c * ((frameNormalization n p : ℂ) * (∑ i, b i * (realProductFrame n s i : ℂ)))
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem complexFrameCoefficientEmbedding_injective (n : ℕ) (p : ℝ) :
    Function.Injective (complexFrameCoefficientEmbedding n p) := by
  intro b c h
  apply complexProductFrameEval_injective n
  funext s
  have hs := congrArg (fun z => z s) h
  change (frameNormalization n p : ℂ) * complexProductFrameEval n b s =
    (frameNormalization n p : ℂ) * complexProductFrameEval n c s at hs
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (frameNormalization_pos n p).ne') hs

instance complexFrameCoefficientNormedAddCommGroup (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] : NormedAddCommGroup (ComplexFrameCoefficient n p) :=
  NormedAddCommGroup.induced (ComplexFrameCoefficient n p)
    (PiLp (ENNReal.ofReal p) (fun _ : FrameIndex n => ℂ))
    (complexFrameCoefficientEmbedding n p) (complexFrameCoefficientEmbedding_injective n p)

instance complexFrameCoefficientNormedSpace (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] : NormedSpace ℂ (ComplexFrameCoefficient n p) :=
  NormedSpace.induced ℂ (ComplexFrameCoefficient n p)
    (PiLp (ENNReal.ofReal p) (fun _ : FrameIndex n => ℂ)) (complexFrameCoefficientEmbedding n p)

instance complexFrameCoefficientRealNormedSpace (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] : NormedSpace ℝ (ComplexFrameCoefficient n p) :=
  NormedSpace.induced ℝ (ComplexFrameCoefficient n p)
    (PiLp (ENNReal.ofReal p) (fun _ : FrameIndex n => ℂ))
    ((complexFrameCoefficientEmbedding n p).restrictScalars ℝ)

instance complexFrameCoefficientCompleteSpace (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] : CompleteSpace (ComplexFrameCoefficient n p) :=
  FiniteDimensional.complete ℂ (ComplexFrameCoefficient n p)

def complexFrameCoefficientIsometry (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    ComplexFrameCoefficient n p →ₗᵢ[ℂ] PiLp (ENNReal.ofReal p) (fun _ : FrameIndex n => ℂ) where
  toLinearMap := complexFrameCoefficientEmbedding n p
  norm_map' _ := rfl

theorem complexFrameCoefficient_norm (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (b : ComplexFrameCoefficient n p) :
    ‖b‖ = frameNormalization n p *
      ‖WithLp.toLp (ENNReal.ofReal p) (complexProductFrameEval n b)‖ := by
  change ‖complexFrameCoefficientEmbedding n p b‖ = _
  have heq : complexFrameCoefficientEmbedding n p b = (frameNormalization n p : ℂ) •
      WithLp.toLp (ENNReal.ofReal p) (complexProductFrameEval n b) := rfl
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (frameNormalization_pos n p)]

theorem complexFrameCoefficient_norm_rpow (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) (b : ComplexFrameCoefficient n p) :
    ‖b‖ ^ p = finiteAverage (fun s => ‖complexProductFrameEval n b s‖ ^ p) := by
  have h4 : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) n
  have hp' : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hs : 0 ≤ ∑ s, ‖complexProductFrameEval n b s‖ ^ p :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [complexFrameCoefficient_norm,
    Real.mul_rpow (frameNormalization_pos n p).le (norm_nonneg _)]
  rw [frameNormalization, ← Real.rpow_mul h4.le]
  have he : (-1 / p) * p = -1 := by field_simp
  rw [he, Real.rpow_neg_one, PiLp.norm_eq_sum (by rwa [hp'])]
  simp only [hp', PiLp.toLp_apply]
  rw [← Real.rpow_mul hs, one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [finiteAverage, frameIndex_card, Nat.cast_pow, Nat.cast_ofNat]

end ComplementedSubspace
