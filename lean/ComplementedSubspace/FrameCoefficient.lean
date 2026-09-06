import ComplementedSubspace.FrameProjectionRange

/-!
# The actual normed coefficient space of the finite frame

The carrier is the coefficient vector space, with the norm induced by the
normalized evaluation map into the finite counting-norm PiLp space. It is a
fresh type synonym so that the coefficient norm cannot be confused with the
default supremum or Euclidean norm on the same coordinate vectors.
-/

noncomputable section
open scoped BigOperators ENNReal

namespace ComplementedSubspace

def FrameCoefficient (n : ℕ) (p : ℝ) := MomentIndex n → ℝ

instance (n : ℕ) (p : ℝ) : AddCommGroup (FrameCoefficient n p) :=
  inferInstanceAs (AddCommGroup (MomentIndex n → ℝ))

instance (n : ℕ) (p : ℝ) : Module ℝ (FrameCoefficient n p) :=
  inferInstanceAs (Module ℝ (MomentIndex n → ℝ))

instance (n : ℕ) (p : ℝ) : FiniteDimensional ℝ (FrameCoefficient n p) :=
  inferInstanceAs (FiniteDimensional ℝ (MomentIndex n → ℝ))

def frameNormalization (n : ℕ) (p : ℝ) : ℝ := ((4 : ℝ) ^ n) ^ (-1 / p)

theorem frameNormalization_pos (n : ℕ) (p : ℝ) : 0 < frameNormalization n p :=
  Real.rpow_pos_of_pos (pow_pos (by norm_num) n) _

def frameCoefficientEmbedding (n : ℕ) (p : ℝ) :
    FrameCoefficient n p →ₗ[ℝ]
      PiLp (ENNReal.ofReal p) (fun _ : FrameIndex n => ℝ) where
  toFun b := WithLp.toLp (ENNReal.ofReal p)
    (fun s => frameNormalization n p * productFrameEval n b s)
  map_add' b c := by
    ext s
    change frameNormalization n p * (∑ i, (b i + c i) * realProductFrame n s i) =
      frameNormalization n p * (∑ i, b i * realProductFrame n s i) +
      frameNormalization n p * (∑ i, c i * realProductFrame n s i)
    simp [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c b := by
    ext s
    change frameNormalization n p * (∑ i, (c * b i) * realProductFrame n s i) =
      c * (frameNormalization n p * (∑ i, b i * realProductFrame n s i))
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem frameCoefficientEmbedding_injective (n : ℕ) (p : ℝ) :
    Function.Injective (frameCoefficientEmbedding n p) := by
  intro b c h
  apply productFrameEval_injective n
  funext s
  have hs := congrArg (fun z => z s) h
  change frameNormalization n p * productFrameEval n b s =
    frameNormalization n p * productFrameEval n c s at hs
  exact mul_left_cancel₀ (ne_of_gt (frameNormalization_pos n p)) hs

instance frameCoefficientNormedAddCommGroup (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] : NormedAddCommGroup (FrameCoefficient n p) :=
  NormedAddCommGroup.induced (FrameCoefficient n p)
    (PiLp (ENNReal.ofReal p) (fun _ : FrameIndex n => ℝ))
    (frameCoefficientEmbedding n p) (frameCoefficientEmbedding_injective n p)

instance frameCoefficientNormedSpace (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] : NormedSpace ℝ (FrameCoefficient n p) :=
  NormedSpace.induced ℝ (FrameCoefficient n p)
    (PiLp (ENNReal.ofReal p) (fun _ : FrameIndex n => ℝ))
    (frameCoefficientEmbedding n p)

instance frameCoefficientCompleteSpace (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] : CompleteSpace (FrameCoefficient n p) :=
  FiniteDimensional.complete ℝ (FrameCoefficient n p)

/-- This map is isometric by the actual induced norm, not by an assumed bound. -/
def frameCoefficientIsometry (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    FrameCoefficient n p →ₗᵢ[ℝ]
      PiLp (ENNReal.ofReal p) (fun _ : FrameIndex n => ℝ) where
  toLinearMap := frameCoefficientEmbedding n p
  norm_map' _ := rfl

theorem frameCoefficient_norm (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (b : FrameCoefficient n p) :
    ‖b‖ = frameNormalization n p *
      ‖WithLp.toLp (ENNReal.ofReal p) (productFrameEval n b)‖ := by
  change ‖frameCoefficientEmbedding n p b‖ = _
  have heq : frameCoefficientEmbedding n p b = frameNormalization n p •
      WithLp.toLp (ENNReal.ofReal p) (productFrameEval n b) := rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (frameNormalization_pos n p)]

end ComplementedSubspace
