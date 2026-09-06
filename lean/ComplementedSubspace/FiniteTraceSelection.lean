import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The scalar part of the finite trace-selection principle

The input t_i are the traces of compressed rank-one coordinate maps. This
module proves only the numerical selection step; the operator proof of the
trace-defect hypothesis is a separate obligation.
-/

noncomputable section
open scoped BigOperators

namespace ComplementedSubspace

theorem abs_le_twice_trace_defect {t : ℝ} (ht : ¬ |t - 1| ≤ 1 / 2) :
    |t| ≤ 2 * |t - t ^ 2| := by
  have hhalf : (1 / 2 : ℝ) ≤ |t - 1| := (lt_of_not_ge ht).le
  have hmul := mul_le_mul_of_nonneg_left hhalf (abs_nonneg t)
  have heq : |t - t ^ 2| = |t| * |t - 1| := by
    rw [show t - t ^ 2 = -(t * (t - 1)) by ring, abs_neg, abs_mul]
  rw [heq]
  nlinarith

/-- Small total trace defect gives at most 3q selected coordinates carrying
almost all the trace. The index type is finite; no summability is assumed. -/
theorem exists_finite_trace_selection {ι : Type*} [Fintype ι]
    (t : ι → ℝ) {q η : ℝ} (hq : 0 ≤ q) (hη : η ≤ 1 / 8)
    (htrace : (∑ i, t i) = q)
    (hdefect : (∑ i, |t i - t i ^ 2|) ≤ 2 * η * q) :
    ∃ s : Finset ι,
      (s.card : ℝ) ≤ 3 * q ∧
      (1 - 4 * η) * q ≤ ∑ i ∈ s, t i ∧
      (∑ i ∈ s, t i) ≤ (1 + 4 * η) * q ∧
      ∀ i ∈ s, 1 / 2 ≤ t i := by
  classical
  let s : Finset ι := Finset.univ.filter fun i => |t i - 1| ≤ 1 / 2
  have hselected (i : ι) (hi : i ∈ s) : 1 / 2 ≤ t i := by
    have habs := (Finset.mem_filter.mp hi).2
    have hlo := (abs_le.mp habs).1
    linarith
  have hout (i : ι) (hi : i ∈ sᶜ) : |t i| ≤ 2 * |t i - t i ^ 2| := by
    apply abs_le_twice_trace_defect
    simpa only [Finset.mem_compl, s, Finset.mem_filter, Finset.mem_univ, true_and]
      using hi
  have hsumdef : (∑ i ∈ sᶜ, |t i - t i ^ 2|) ≤ ∑ i, |t i - t i ^ 2| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => abs_nonneg _)
  have houtside : |∑ i ∈ sᶜ, t i| ≤ 4 * η * q := by
    calc
      |∑ i ∈ sᶜ, t i| ≤ ∑ i ∈ sᶜ, |t i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ sᶜ, 2 * |t i - t i ^ 2| := Finset.sum_le_sum hout
      _ = 2 * ∑ i ∈ sᶜ, |t i - t i ^ 2| := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ∑ i, |t i - t i ^ 2| := mul_le_mul_of_nonneg_left hsumdef (by norm_num)
      _ ≤ 2 * (2 * η * q) := mul_le_mul_of_nonneg_left hdefect (by norm_num)
      _ = 4 * η * q := by ring
  have hsplit : (∑ i ∈ s, t i) + (∑ i ∈ sᶜ, t i) = q :=
    (Finset.sum_add_sum_compl s t).trans htrace
  have hbounds := abs_le.mp houtside
  have hlo : (1 - 4 * η) * q ≤ ∑ i ∈ s, t i := by nlinarith
  have hhi : (∑ i ∈ s, t i) ≤ (1 + 4 * η) * q := by nlinarith
  have hcard : (s.card : ℝ) * (1 / 2) ≤ ∑ i ∈ s, t i := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun i hi => hselected i hi))
  have hηq := mul_le_mul_of_nonneg_right hη hq
  refine ⟨s, ?_, hlo, hhi, hselected⟩
  nlinarith

end ComplementedSubspace
