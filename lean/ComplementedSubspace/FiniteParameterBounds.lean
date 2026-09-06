import ComplementedSubspace.FiniteParameterGap
import Mathlib.Analysis.MeanInequalities

/-!
# Comparison of the finite-frame scalar scales

The distinguished witness scale `g`, uniform Hilbert comparison `H`, and
overlap scale `L` are separate constants. Finite scalar Hölder proves `L ≤ g`,
and the elementary bound on the scalar moment proves `g ≤ H`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

theorem frameConjugate_holder {p : ℝ} (hp : 1 < p) :
    p.HolderConjugate (frameConjugate p) :=
  Real.HolderConjugate.conjExponent hp

private theorem sqrt_two_rpow (r : ℝ) :
    Real.sqrt 2 ^ r = (2 : ℝ) ^ (r / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Scalar Hölder for the three nonzero entries of the four-point frame. -/
theorem realFrame_scalar_holder {p q : ℝ} (hpq : p.HolderConjugate q) :
    (4 : ℝ) ≤ ((2 : ℝ) ^ (p / 2) + 2) ^ (1 / p) *
      ((2 : ℝ) ^ (q / 2) + 2) ^ (1 / q) := by
  let v : Fin 3 → ℝ := fun i => if i = 0 then Real.sqrt 2 else 1
  have hv : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ v i := by
    intro i _
    dsimp [v]
    split_ifs <;> positivity
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ (f := v) (g := v) hpq hv hv
  have hleft : (∑ i : Fin 3, v i * v i) = 4 := by
    norm_num [v, Fin.sum_univ_succ, ← sq, Real.sq_sqrt]
  have hright (r : ℝ) : (∑ i : Fin 3, v i ^ r) = (2 : ℝ) ^ (r / 2) + 2 := by
    norm_num [v, Fin.sum_univ_succ, sqrt_two_rpow]
  simpa only [hleft, hright] using h

theorem realFrameLogAlpha_add_conjugate_nonneg {p : ℝ} (hp : 1 < p) :
    0 ≤ realFrameLogAlpha p + realFrameLogAlpha (frameConjugate p) := by
  have hpq := frameConjugate_holder hp
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (realFrame_scalar_holder hpq)
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by positivity)] at h
  have hi := hpq.inv_add_inv_eq_one
  unfold realFrameLogAlpha
  rw [Real.log_div (by positivity) (by norm_num),
    Real.log_div (by positivity) (by norm_num)]
  simp only [div_eq_mul_inv, one_mul] at h ⊢
  nlinarith [congrArg (fun t : ℝ => Real.log 4 * t) hi]

theorem realFrameAlpha_mul_conjugate_ge_one {p : ℝ} (hp : 1 < p) :
    1 ≤ realFrameAlpha p * realFrameAlpha (frameConjugate p) := by
  rw [realFrameAlpha, realFrameAlpha, ← Real.exp_add, Real.one_le_exp_iff]
  exact realFrameLogAlpha_add_conjugate_nonneg hp

theorem realFrameLogAlpha_le_hilbert {p : ℝ} (hp : 2 ≤ p) :
    realFrameLogAlpha p ≤ (1 / 2 - 1 / p) * Real.log 2 := by
  have hp0 : 0 < p := by linarith
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (p / 2) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (1 : ℝ) ≤ p / 2 by linarith)
  have hmoment : ((2 : ℝ) ^ (p / 2) + 2) / 4 ≤ (2 : ℝ) ^ (p / 2) / 2 := by
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) <
    ((2 : ℝ) ^ (p / 2) + 2) / 4) hmoment
  calc
    realFrameLogAlpha p ≤ Real.log ((2 : ℝ) ^ (p / 2) / 2) / p :=
      div_le_div_of_nonneg_right hlog hp0.le
    _ = (1 / 2 - 1 / p) * Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow (by norm_num)]
      field_simp
      <;> ring

theorem realFrameWitnessScale_le_hilbertScale (n : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    realFrameWitnessScale n p ≤ realFrameHilbertScale n p := by
  apply Real.exp_le_exp.2
  exact (mul_le_mul_of_nonneg_left (realFrameLogAlpha_le_hilbert hp)
    (Nat.cast_nonneg n)).trans_eq (by ring)

theorem realFrameLogOverlap_le_logAlpha {p : ℝ} (hp : 2 ≤ p) :
    realFrameLogOverlap p ≤ realFrameLogAlpha p := by
  have hα := realFrameLogAlpha_add_conjugate_nonneg (by linarith : 1 < p)
  have hε : 0 ≤ p - 2 := sub_nonneg.2 hp
  have hp0 : 0 < p := by linarith
  have ht : 0 ≤ (p - 2) / (2 * p) * Real.log (5 / 4 : ℝ) := by positivity
  have hH : 0 ≤ 2 * (p - 2) ^ 2 / p ^ 2 * Real.log 2 := by positivity
  unfold realFrameLogOverlap
  linarith

theorem realFrameOverlapScale_le_witnessScale (n : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    realFrameOverlapScale n p ≤ realFrameWitnessScale n p := by
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
    (realFrameLogOverlap_le_logAlpha hp) (Nat.cast_nonneg n))

theorem realFrame_scales_ordered (n : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    realFrameOverlapScale n p ≤ realFrameWitnessScale n p ∧
      realFrameWitnessScale n p ≤ realFrameHilbertScale n p :=
  ⟨realFrameOverlapScale_le_witnessScale n hp,
    realFrameWitnessScale_le_hilbertScale n hp⟩

theorem realFrameAlpha_eq_rpow (r : ℝ) :
    realFrameAlpha r = (((2 : ℝ) ^ (r / 2) + 2) / 4) ^ (1 / r) := by
  rw [Real.rpow_def_of_pos (by positivity)]
  unfold realFrameAlpha realFrameLogAlpha
  congr 1
  ring

/-- Powered witness norm, convenient for connecting to finite moment identities. -/
theorem realFrameWitnessScale_rpow (n : ℕ) {p : ℝ} (hp : p ≠ 0) :
    realFrameWitnessScale n p ^ p = (((2 : ℝ) ^ (p / 2) + 2) / 4) ^ n := by
  rw [realFrameWitnessScale_eq, ← Real.rpow_natCast,
    ← Real.rpow_mul (realFrameAlpha_pos p).le, mul_comm (n : ℝ),
    Real.rpow_mul (realFrameAlpha_pos p).le, Real.rpow_natCast,
    realFrameAlpha_rpow hp]

end ComplementedSubspace
