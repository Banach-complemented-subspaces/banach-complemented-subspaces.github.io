import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# Quadratic perturbation of finite orthogonal projections near exponent two

The scalar estimate uses only a first derivative on `[0,1]`, including at zero.
It is the analytic ingredient in the fixed-frame construction.
-/

noncomputable section

open scoped BigOperators
open Set

namespace ComplementedSubspace

/-- Difference between the scalar `p`-energy and the Euclidean energy. -/
def powerEnergyDifference (p t : ℝ) : ℝ := t ^ p - t ^ (2 : ℕ)

lemma rpow_sub_one_close_to_self {p t : ℝ} (hp : 2 ≤ p)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ t - t ^ (p - 1) ∧ t - t ^ (p - 1) ≤ p - 2 := by
  have hupper : t ^ (p - 1) ≤ t := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' ht.1 ht.2
      (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ p - 1)
  have hlower := one_add_mul_self_le_rpow_one_add
    (s := t - 1) (p := p - 1) (by linarith [ht.1] : -1 ≤ t - 1)
    (by linarith : 1 ≤ p - 1)
  have hlower' : 1 + (p - 1) * (t - 1) ≤ t ^ (p - 1) := by
    simpa only [show 1 + (t - 1) = t by ring] using hlower
  constructor
  · linarith
  · nlinarith [mul_nonneg (show 0 ≤ p - 2 by linarith) ht.1]

lemma powerEnergyDifference_hasDerivAt {p : ℝ} (hp : 2 ≤ p) (t : ℝ) :
    HasDerivAt (powerEnergyDifference p) (p * t ^ (p - 1) - 2 * t) t := by
  convert! (Real.hasDerivAt_rpow_const (x := t) (p := p)
    (Or.inr (by linarith : 1 ≤ p))).sub ((hasDerivAt_id t).pow 2) using 1 <;>
    simp [powerEnergyDifference]

lemma powerEnergyDifference_deriv_bound {p t : ℝ} (hp : 2 ≤ p)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |p * t ^ (p - 1) - 2 * t| ≤ 3 * (p - 2) := by
  obtain ⟨h0, h1⟩ := rpow_sub_one_close_to_self hp ht
  have hpow0 := Real.rpow_nonneg ht.1 (p - 1)
  have hpow1 : t ^ (p - 1) ≤ 1 := by linarith [ht.2]
  have hprod0 := mul_nonneg (show 0 ≤ p - 2 by linarith) hpow0
  have hprod1 := mul_nonneg (show 0 ≤ p - 2 by linarith)
    (show 0 ≤ 1 - t ^ (p - 1) by linarith)
  apply abs_le.mpr
  constructor <;> nlinarith

lemma powerEnergyDifference_lipschitz {p s t : ℝ} (hp : 2 ≤ p)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |powerEnergyDifference p s - powerEnergyDifference p t| ≤
      3 * (p - 2) * |s - t| := by
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => (powerEnergyDifference_hasDerivAt hp x).differentiableAt)
    (fun x hx => by
      rw [(powerEnergyDifference_hasDerivAt hp x).deriv, Real.norm_eq_abs]
      exact powerEnergyDifference_deriv_bound hp hx) ht hs
  simpa only [Real.norm_eq_abs] using h

/-- The energy estimate needed for a normalized Euclidean orthogonal projection.
The hypotheses are precisely its coordinate bounds and Pythagorean identity. -/
lemma finite_projection_energy_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 2 ≤ p) (x a : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (ha : ∀ i, |a i| ≤ 1)
    (horth : (∑ i, (a i) ^ 2) + (∑ i, (x i - a i) ^ 2) = ∑ i, (x i) ^ 2) :
    (∑ i, |a i| ^ p) ≤ (∑ i, |x i| ^ p) +
      (9 / 4 : ℝ) * Fintype.card ι * (p - 2) ^ 2 := by
  have hcoord (i : ι) :
      |a i| ^ p - |x i| ^ p ≤ (a i) ^ 2 - (x i) ^ 2 +
        (x i - a i) ^ 2 + (9 / 4 : ℝ) * (p - 2) ^ 2 := by
    have hlip := powerEnergyDifference_lipschitz hp
      (show |a i| ∈ Icc (0 : ℝ) 1 from ⟨abs_nonneg _, ha i⟩)
      (show |x i| ∈ Icc (0 : ℝ) 1 from ⟨abs_nonneg _, hx i⟩)
    have habs : |powerEnergyDifference p (|a i|) - powerEnergyDifference p (|x i|)| ≤
        3 * (p - 2) * |x i - a i| := by
      refine hlip.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ 3 * (p - 2))
      simpa only [abs_sub_comm] using abs_abs_sub_abs_le_abs_sub (a i) (x i)
    have hsq := sq_nonneg (|x i - a i| - 3 / 2 * (p - 2))
    have hu := (abs_le.mp habs).2
    simp only [powerEnergyDifference, sq_abs] at hu
    nlinarith [sq_abs (x i - a i)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoord i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  nlinarith

end ComplementedSubspace
