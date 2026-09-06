import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit finite-frame parameters and the positive overlap gap

The four-point real frame has scalar moment `(2^(r/2)+2)/4`.
We retain separate constants for frame-supported witnesses and uniform norm
comparison. The overlap scale is the revised finite-frame scale, whose logarithm
has derivative `log(32/25)/8` per tensor factor at exponent two.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Topology

namespace ComplementedSubspace

/-- Logarithm of the scalar moment root for the four-point real frame. -/
def realFrameLogAlpha (r : ℝ) : ℝ :=
  Real.log (((2 : ℝ) ^ (r / 2) + 2) / 4) / r

/-- Scalar moment root. This constant describes frame-supported directions. -/
def realFrameAlpha (r : ℝ) : ℝ := Real.exp (realFrameLogAlpha r)

/-- Conjugate exponent, used only at exponents greater than one. -/
def frameConjugate (p : ℝ) : ℝ := p / (p - 1)

/-- Logarithm of the revised overlap scale, per tensor factor. -/
def realFrameLogOverlap (p : ℝ) : ℝ :=
  -realFrameLogAlpha (frameConjugate p) -
    (p - 2) / (2 * p) * Real.log (5 / 4 : ℝ) -
    2 * (p - 2) ^ 2 / p ^ 2 * Real.log 2

/-- The large norm of the distinguished frame-supported witnesses. -/
def realFrameWitnessScale (n : ℕ) (p : ℝ) : ℝ :=
  Real.exp ((n : ℝ) * realFrameLogAlpha p)

/-- The uniform upper Hilbert comparison bound, distinct from the witness scale. -/
def realFrameHilbertScale (n : ℕ) (p : ℝ) : ℝ :=
  Real.exp ((n : ℝ) * (1 / 2 - 1 / p) * Real.log 2)

/-- Revised overlap scale for the real finite-frame construction. -/
def realFrameOverlapScale (n : ℕ) (p : ℝ) : ℝ :=
  Real.exp ((n : ℝ) * realFrameLogOverlap p)

@[simp] theorem realFrameLogAlpha_two : realFrameLogAlpha 2 = 0 := by
  norm_num [realFrameLogAlpha]

@[simp] theorem frameConjugate_two : frameConjugate 2 = 2 := by
  norm_num [frameConjugate]

@[simp] theorem realFrameLogOverlap_two : realFrameLogOverlap 2 = 0 := by
  simp [realFrameLogOverlap]

theorem realFrameAlpha_pos (r : ℝ) : 0 < realFrameAlpha r := Real.exp_pos _

theorem realFrameOverlapScale_pos (n : ℕ) (p : ℝ) :
    0 < realFrameOverlapScale n p := Real.exp_pos _

theorem hasDerivAt_realFrameLogAlpha_two :
    HasDerivAt realFrameLogAlpha (Real.log 2 / 8) 2 := by
  have hpow : HasDerivAt (fun r : ℝ => (2 : ℝ) ^ (r / 2)) (Real.log 2) 2 := by
    convert ((hasDerivAt_id (2 : ℝ)).div_const 2).const_rpow
      (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num <;> ring
  have hmoment := (hpow.add_const 2).div_const 4
  have hlog := hmoment.log (by norm_num : ((2 : ℝ) ^ ((2 : ℝ) / 2) + 2) / 4 ≠ 0)
  convert! hlog.div (hasDerivAt_id (2 : ℝ)) (by norm_num) using 1 <;>
    norm_num [realFrameLogAlpha] <;> ring

theorem hasDerivAt_frameConjugate_two : HasDerivAt frameConjugate (-1) 2 := by
  convert! (hasDerivAt_id (2 : ℝ)).div ((hasDerivAt_id (2 : ℝ)).sub_const 1)
    (by norm_num : (2 : ℝ) - 1 ≠ 0) using 1 <;> norm_num [frameConjugate]

theorem realFrame_gap_constant_eq :
    Real.log 2 / 8 - Real.log (5 / 4 : ℝ) / 4 = Real.log (32 / 25 : ℝ) / 8 := by
  have h := Real.log_div (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (5 / 4 : ℝ) ^ 2 ≠ 0)
  rw [Real.log_pow] at h
  norm_num at h
  linarith

theorem realFrame_gap_constant_pos : 0 < Real.log (32 / 25 : ℝ) / 8 :=
  div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem hasDerivAt_realFrameLogOverlap_two :
    HasDerivAt realFrameLogOverlap (Real.log (32 / 25 : ℝ) / 8) 2 := by
  have ha : HasDerivAt realFrameLogAlpha (Real.log 2 / 8) (frameConjugate 2) := by
    simpa using hasDerivAt_realFrameLogAlpha_two
  have hα := ha.comp 2 hasDerivAt_frameConjugate_two
  have hε := (hasDerivAt_id (2 : ℝ)).sub_const 2
  have hfirst : HasDerivAt (fun p : ℝ => (p - 2) / (2 * p)) (1 / 4) 2 := by
    convert! hε.div ((hasDerivAt_id (2 : ℝ)).const_mul 2)
      (by norm_num : (2 : ℝ) * 2 ≠ 0) using 1 <;> norm_num
  have hsecond : HasDerivAt (fun p : ℝ => 2 * (p - 2) ^ 2 / p ^ 2) 0 2 := by
    convert! ((hε.pow 2).const_mul 2).div ((hasDerivAt_id (2 : ℝ)).pow 2)
      (by norm_num : (2 : ℝ) ^ 2 ≠ 0) using 1 <;> norm_num
  have h := (hα.neg.sub (hfirst.mul_const (Real.log (5 / 4 : ℝ)))).sub
    (hsecond.mul_const (Real.log 2))
  convert! h using 1
  simp only [mul_neg_one, neg_neg, zero_mul, sub_zero]
  rw [← realFrame_gap_constant_eq]
  ring

/-- Cubic tensor order; shifting the natural index removes the zero denominator. -/
def finiteParameterOrder (k : ℕ) : ℕ := (k + 1) ^ 3

/-- Reciprocal-square distance of the exponent from two. -/
def finiteParameterEpsilon (k : ℕ) : ℝ := (1 / ((k : ℝ) + 1)) ^ 2

def finiteParameterExponent (k : ℕ) : ℝ := 2 + finiteParameterEpsilon k

theorem finiteParameterOrder_pos (k : ℕ) : 0 < finiteParameterOrder k := by
  simp [finiteParameterOrder]

theorem finiteParameterEpsilon_pos (k : ℕ) : 0 < finiteParameterEpsilon k := by
  unfold finiteParameterEpsilon
  positivity

theorem finiteParameterEpsilon_le_one (k : ℕ) : finiteParameterEpsilon k ≤ 1 := by
  have h : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have h0 : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
  unfold finiteParameterEpsilon
  nlinarith

theorem finiteParameterExponent_bounds (k : ℕ) :
    2 < finiteParameterExponent k ∧ finiteParameterExponent k ≤ 3 := by
  have h0 := finiteParameterEpsilon_pos k
  have h1 := finiteParameterEpsilon_le_one k
  constructor <;> unfold finiteParameterExponent <;> linarith

theorem finiteParameter_linear_identity (k : ℕ) :
    (finiteParameterOrder k : ℝ) * finiteParameterEpsilon k = (k : ℝ) + 1 := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [finiteParameterOrder, finiteParameterEpsilon, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

theorem finiteParameter_quadratic_identity (k : ℕ) :
    (finiteParameterOrder k : ℝ) * finiteParameterEpsilon k ^ 2 =
      1 / ((k : ℝ) + 1) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [finiteParameterOrder, finiteParameterEpsilon, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

theorem finiteParameterEpsilon_tendsto :
    Tendsto finiteParameterEpsilon atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ 2) atTop (𝓝 0)
  simpa [finiteParameterEpsilon] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2

theorem finiteParameterExponent_tendsto :
    Tendsto finiteParameterExponent atTop (𝓝 2) := by
  change Tendsto (fun k => 2 + finiteParameterEpsilon k) atTop (𝓝 2)
  simpa [finiteParameterExponent] using
    tendsto_const_nhds.add finiteParameterEpsilon_tendsto

theorem finiteParameter_linear_tendsto :
    Tendsto (fun k => (finiteParameterOrder k : ℝ) * finiteParameterEpsilon k)
      atTop atTop := by
  simp only [finiteParameter_linear_identity]
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem finiteParameter_quadratic_tendsto :
    Tendsto (fun k => (finiteParameterOrder k : ℝ) * finiteParameterEpsilon k ^ 2)
      atTop (𝓝 0) := by
  simpa only [finiteParameter_quadratic_identity] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem finiteParameter_gap_ratio_tendsto :
    Tendsto (fun k => realFrameLogOverlap (finiteParameterExponent k) /
      finiteParameterEpsilon k) atTop (𝓝 (Real.log (32 / 25 : ℝ) / 8)) := by
  have hp : Tendsto finiteParameterExponent atTop (𝓝[≠] (2 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨finiteParameterExponent_tendsto, Eventually.of_forall ?_⟩
    intro k
    simpa using (finiteParameterExponent_bounds k).1.ne'
  have h := hasDerivAt_realFrameLogOverlap_two.tendsto_slope.comp hp
  simpa only [Function.comp_def, slope_def_field, realFrameLogOverlap_two,
    sub_zero, finiteParameterExponent, add_sub_cancel_left] using h

/-- The strict positive derivative makes the revised overlap scale diverge. -/
theorem finiteParameter_logOverlap_tendsto :
    Tendsto (fun k => (finiteParameterOrder k : ℝ) *
      realFrameLogOverlap (finiteParameterExponent k)) atTop atTop := by
  have h := finiteParameter_linear_tendsto.atTop_mul_pos
    realFrame_gap_constant_pos finiteParameter_gap_ratio_tendsto
  apply h.congr
  intro k
  have hε := (finiteParameterEpsilon_pos k).ne'
  field_simp

theorem finiteParameter_overlap_tendsto :
    Tendsto (fun k => realFrameOverlapScale (finiteParameterOrder k)
      (finiteParameterExponent k)) atTop atTop :=
  Real.tendsto_exp_atTop.comp finiteParameter_logOverlap_tendsto

/-- Any requested growth and error tolerances can be met simultaneously. -/
theorem exists_finiteFrame_parameters {δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    ∃ n : ℕ, ∃ p : ℝ, 0 < n ∧ 2 < p ∧ p ≤ 3 ∧
      p - 2 < δ ∧ (n : ℝ) * (p - 2) ^ 2 < δ ∧
      R < realFrameOverlapScale n p := by
  have hε := finiteParameterEpsilon_tendsto.eventually (gt_mem_nhds hδ)
  have hquad := finiteParameter_quadratic_tendsto.eventually (gt_mem_nhds hδ)
  have hL := finiteParameter_overlap_tendsto.eventually_gt_atTop R
  obtain ⟨k, hkε, hkquad, hkL⟩ := (hε.and (hquad.and hL)).exists
  refine ⟨finiteParameterOrder k, finiteParameterExponent k, finiteParameterOrder_pos k,
    (finiteParameterExponent_bounds k).1, (finiteParameterExponent_bounds k).2, ?_, ?_, hkL⟩
  · simpa only [finiteParameterExponent, add_sub_cancel_left] using hkε
  · simpa only [finiteParameterExponent, add_sub_cancel_left] using hkquad

/-- The exponential definition agrees with the usual scalar moment root. -/
theorem realFrameAlpha_rpow {r : ℝ} (hr : r ≠ 0) :
    realFrameAlpha r ^ r = ((2 : ℝ) ^ (r / 2) + 2) / 4 := by
  have hm : (0 : ℝ) < ((2 : ℝ) ^ (r / 2) + 2) / 4 := by positivity
  rw [realFrameAlpha, ← Real.exp_mul, realFrameLogAlpha, div_mul_cancel₀ _ hr,
    Real.exp_log hm]

theorem realFrameWitnessScale_eq (n : ℕ) (p : ℝ) :
    realFrameWitnessScale n p = realFrameAlpha p ^ n := by
  rw [realFrameWitnessScale, realFrameAlpha, Real.exp_nat_mul]

theorem realFrameHilbertScale_eq (n : ℕ) (p : ℝ) :
    realFrameHilbertScale n p = (2 : ℝ) ^ ((n : ℝ) * (1 / 2 - 1 / p)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold realFrameHilbertScale
  congr 1
  ring

/-- Exact correspondence with the revised product formula from the proof notes. -/
theorem realFrameOverlapScale_eq (n : ℕ) {p : ℝ} (hp : p ≠ 0) :
    realFrameOverlapScale n p =
      realFrameAlpha (frameConjugate p) ^ (-(n : ℝ)) *
      (5 / 4 : ℝ) ^ (-(n : ℝ) * (p - 2) / (2 * p)) *
      realFrameHilbertScale n p ^ (-4 * (p - 2) / p) := by
  simp only [realFrameAlpha, realFrameHilbertScale, ← Real.exp_mul,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5 / 4), ← Real.exp_add]
  unfold realFrameOverlapScale realFrameLogOverlap
  congr 1
  field_simp
  <;> ring

end ComplementedSubspace
