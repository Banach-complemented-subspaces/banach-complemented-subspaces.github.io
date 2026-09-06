import ComplementedSubspace.FiniteSignsComplex
import Mathlib.Analysis.MeanInequalities

noncomputable section
namespace ComplementedSubspace

theorem sum_geometric_le {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (∑ i, (f i) ^ t * (g i) ^ (1 - t)) ≤
      (∑ i, f i) ^ t * (∑ i, g i) ^ (1 - t) := by
  rcases eq_or_lt_of_le ht₀ with rfl | ht₀
  · simp
  rcases eq_or_lt_of_le ht₁ with rfl | ht₁
  · simp
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i => (f i) ^ t) (g := fun i => (g i) ^ (1 - t))
    (Real.HolderConjugate.inv_one_sub_inv ht₀ ht₁)
    (fun i _ => Real.rpow_nonneg (hf i) _)
    (fun i _ => Real.rpow_nonneg (hg i) _)
  have hp (i : ι) : ((f i) ^ t) ^ t⁻¹ = f i := by
    rw [← Real.rpow_mul (hf i), mul_inv_cancel₀ ht₀.ne', Real.rpow_one]
  have hq (i : ι) : ((g i) ^ (1 - t)) ^ (1 - t)⁻¹ = g i := by
    rw [← Real.rpow_mul (hg i), mul_inv_cancel₀ (by linarith : 1 - t ≠ 0), Real.rpow_one]
  simpa only [hp, hq, one_div, inv_inv] using h

theorem finiteAverage_geometric_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    finiteAverage (fun i => (f i) ^ t * (g i) ^ (1 - t)) ≤
      (finiteAverage f) ^ t * (finiteAverage g) ^ (1 - t) := by
  let w : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hw : 0 < w := by simp only [w]; positivity
  have h := sum_geometric_le (fun i => w * f i) (fun i => w * g i)
    (fun i => mul_nonneg hw.le (hf i)) (fun i => mul_nonneg hw.le (hg i)) t ht₀ ht₁
  have hid (i : ι) : (w * f i) ^ t * (w * g i) ^ (1 - t) =
      w * ((f i) ^ t * (g i) ^ (1 - t)) := by
    rw [Real.mul_rpow hw.le (hf i), Real.mul_rpow hw.le (hg i)]
    calc
      w ^ t * (f i) ^ t * (w ^ (1 - t) * (g i) ^ (1 - t)) =
          (w ^ t * w ^ (1 - t)) * ((f i) ^ t * (g i) ^ (1 - t)) := by ring
      _ = _ := by rw [← Real.rpow_add hw, add_sub_cancel, Real.rpow_one]
  simp_rw [hid] at h
  simpa only [← Finset.mul_sum, finiteAverage, w] using h

/-- The only interpolation used by the finite overlap argument: an ordinary
finite Hölder inequality between scalar second and fourth moments. -/
theorem finiteAverage_moment_interpolation {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (p : ℝ) (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) :
    finiteAverage (fun i => (f i) ^ p) ≤
      (finiteAverage (fun i => f i ^ 2)) ^ ((4 - p) / 2) *
        (finiteAverage (fun i => f i ^ 4)) ^ ((p - 2) / 2) := by
  have h := finiteAverage_geometric_le (fun i => f i ^ 2) (fun i => f i ^ 4)
    (fun i => sq_nonneg _) (fun i => by positivity)
    ((4 - p) / 2) (by linarith) (by linarith)
  have he : 1 - (4 - p) / 2 = (p - 2) / 2 := by ring
  rw [he] at h
  have hid (i : ι) : (f i ^ 2) ^ ((4 - p) / 2) * (f i ^ 4) ^ ((p - 2) / 2) =
      (f i) ^ p := by
    have ha : 0 ≤ (4 - p) / 2 := by linarith
    have hb : 0 ≤ (p - 2) / 2 := by linarith
    rw [← Real.rpow_natCast_mul (hf i), ← Real.rpow_natCast_mul (hf i),
      ← Real.rpow_add_of_nonneg (hf i) (by positivity) (by positivity)]
    congr 1
    norm_num <;> ring
  simpa only [hid] using h

theorem finiteAverage_moment_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (p A K : ℝ)
    (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (h₂ : finiteAverage (fun i => f i ^ 2) ≤ A)
    (h₄ : finiteAverage (fun i => f i ^ 4) ≤ K * A ^ 2) :
    finiteAverage (fun i => (f i) ^ p) ≤ K ^ ((p - 2) / 2) * A ^ (p / 2) := by
  have ht : 0 ≤ (p - 2) / 2 := by linarith
  have hs : 0 ≤ (4 - p) / 2 := by linarith
  calc
    _ ≤ (finiteAverage (fun i => f i ^ 2)) ^ ((4 - p) / 2) *
        (finiteAverage (fun i => f i ^ 4)) ^ ((p - 2) / 2) :=
      finiteAverage_moment_interpolation f hf p hp₂ hp₄
    _ ≤ A ^ ((4 - p) / 2) * (K * A ^ 2) ^ ((p - 2) / 2) :=
      mul_le_mul (Real.rpow_le_rpow (finiteAverage_nonneg _ (fun _ => sq_nonneg _)) h₂ hs)
        (Real.rpow_le_rpow (finiteAverage_nonneg _ (fun _ => by positivity)) h₄ ht)
        (Real.rpow_nonneg (finiteAverage_nonneg _ (fun _ => by positivity)) _)
        (Real.rpow_nonneg hA _)
    _ = _ := by
      rw [Real.mul_rpow hK (sq_nonneg _), ← Real.rpow_natCast_mul hA]
      rw [mul_left_comm, ← Real.rpow_add_of_nonneg hA hs (by positivity)]
      congr 2
      norm_num <;> ring

theorem realSignSum_moment_le (n : ℕ) (a : Fin n → ℝ)
    (p : ℝ) (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) :
    finiteAverage (fun s => |realSignSum n a s| ^ p) ≤
      (3 : ℝ) ^ ((p - 2) / 2) * (∑ i, a i ^ 2) ^ (p / 2) := by
  apply finiteAverage_moment_bound _ (fun _ => abs_nonneg _) p _ 3 hp₂ hp₄
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)
  · simpa only [sq_abs] using (realSignSum_second_moment n a).le
  · simpa only [Even.pow_abs (by decide : Even 4)] using realSignSum_fourth_moment_le n a

theorem complexSignSum_moment_le (n : ℕ) (a : Fin n → ℂ)
    (p : ℝ) (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4) :
    finiteAverage (fun s => ‖complexSignSum n a s‖ ^ p) ≤
      (3 : ℝ) ^ ((p - 2) / 2) * (∑ i, ‖a i‖ ^ 2) ^ (p / 2) := by
  exact finiteAverage_moment_bound _ (fun _ => norm_nonneg _) p _ 3 hp₂ hp₄
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)
    (complexSignSum_second_moment n a).le (complexSignSum_fourth_moment_le n a)

end ComplementedSubspace
