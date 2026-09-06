import ComplementedSubspace.LocalHilbertCompactness
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Real.Sqrt

/-!
Preservation of approximate parallelogram inequalities by real continuous
duals. The proof uses squared evaluations and operator norms directly. It does
not identify the dual of an l2 sum, choose almost norm-attaining vectors, or
invoke reflexivity.
-/

noncomputable section

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A squared evaluation bound on the unit ball bounds the squared dual norm. -/
lemma dual_norm_sq_le_of_unit_sq (f : StrongDual ℝ E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖x‖ ≤ 1 → (f x) ^ 2 ≤ C) : ‖f‖ ^ 2 ≤ C := by
  have hf : ‖f‖ ≤ Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg C)
    intro x hx
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mp
    calc
      ‖f x‖ ^ 2 = (f x) ^ 2 := by simp only [Real.norm_eq_abs, sq_abs]
      _ ≤ C := h x hx.le
      _ = (Real.sqrt C) ^ 2 := (Real.sq_sqrt hC).symm
  exact ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mpr hf).trans_eq (Real.sq_sqrt hC)

/-- The elementary two-term Cauchy-Schwarz evaluation estimate. -/
lemma dual_pair_eval_sq_le (f g : StrongDual ℝ E) (x y : E) :
    (f x + g y) ^ 2 ≤ (‖f‖ ^ 2 + ‖g‖ ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hf : |f x| ≤ ‖f‖ * ‖x‖ := by simpa only [Real.norm_eq_abs] using f.le_opNorm x
  have hg : |g y| ≤ ‖g‖ * ‖y‖ := by simpa only [Real.norm_eq_abs] using g.le_opNorm y
  have habs : |f x + g y| ≤ ‖f‖ * ‖x‖ + ‖g‖ * ‖y‖ :=
    (abs_add_le (f x) (g y)).trans (add_le_add hf hg)
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs
  rw [sq_abs] at hsq
  nlinarith [sq_nonneg (‖f‖ * ‖y‖ - ‖g‖ * ‖x‖)]

/-- A bound for every paired evaluation controls the sum of the squared dual
norms. Testing at `(f x)•x` and `(g y)•y` eliminates the need for norm attainment. -/
lemma dual_pair_norm_sq_le_of_eval_sq (f g : StrongDual ℝ E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, (f x + g y) ^ 2 ≤ C * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    ‖f‖ ^ 2 + ‖g‖ ^ 2 ≤ C := by
  have hunit (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
      (f x) ^ 2 + (g y) ^ 2 ≤ C := by
    have hnx : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hny : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
    have hh := h ((f x) • x) ((g y) • y)
    simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hh
    have hscaled : C * ((f x) ^ 2 * ‖x‖ ^ 2 + (g y) ^ 2 * ‖y‖ ^ 2) ≤
        C * ((f x) ^ 2 + (g y) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [mul_one] using add_le_add
        (mul_le_mul_of_nonneg_left hnx (sq_nonneg (f x)))
        (mul_le_mul_of_nonneg_left hny (sq_nonneg (g y)))
    have hsquare : ((f x) ^ 2 + (g y) ^ 2) ^ 2 ≤ C * ((f x) ^ 2 + (g y) ^ 2) := by
      have ha : ((f x) ^ 2 + (g y) ^ 2) ^ 2 ≤
          C * ((f x) ^ 2 * ‖x‖ ^ 2 + (g y) ^ 2 * ‖y‖ ^ 2) := by
        convert hh using 1 <;> ring
      exact ha.trans hscaled
    have hnonneg : 0 ≤ (f x) ^ 2 + (g y) ^ 2 := by positivity
    rcases eq_or_lt_of_le hnonneg with hz | hp
    · simpa only [← hz] using hC
    · exact (mul_le_mul_iff_right₀ hp).mp (by simpa only [pow_two, mul_comm] using hsquare)
  have hfirst (y : E) (hy : ‖y‖ ≤ 1) : ‖f‖ ^ 2 + (g y) ^ 2 ≤ C := by
    have hnonneg : 0 ≤ C - (g y) ^ 2 := by
      have hh := hunit 0 y (by simp) hy
      simp only [map_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hh
      linarith
    have hh := dual_norm_sq_le_of_unit_sq f hnonneg (fun x hx => by
      have hh := hunit x y hx hy
      linarith)
    linarith
  have hnonneg : 0 ≤ C - ‖f‖ ^ 2 := by
    have hh := hfirst 0 (by simp)
    simp only [map_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hh
    linarith
  have hh := dual_norm_sq_le_of_unit_sq g hnonneg (fun y hy => by
    have hh := hfirst y hy
    linarith)
  linarith

/-- The approximate parallelogram constant passes to the continuous real dual
without any loss. This is the direct squared-evaluation version of the
Hadamard-adjoint argument. -/
theorem ApproxParallelogram.dual_of_nonneg {ν : ℝ} (hν : 0 ≤ ν)
    (h : ApproxParallelogram (fun x : E => ‖x‖) ν) :
    ApproxParallelogram (fun f : StrongDual ℝ E => ‖f‖) ν := by
  intro f g
  apply dual_pair_norm_sq_le_of_eval_sq (f + g) (f - g) (by positivity)
  intro x y
  have heq : (f + g) x + (f - g) y = f (x + y) + g (x - y) := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, map_add, map_sub]
    ring
  rw [heq]
  calc
    (f (x + y) + g (x - y)) ^ 2 ≤
        (‖f‖ ^ 2 + ‖g‖ ^ 2) * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) :=
      dual_pair_eval_sq_le f g (x + y) (x - y)
    _ ≤ (‖f‖ ^ 2 + ‖g‖ ^ 2) * (2 * ν * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (h x y) (by positivity)
    _ = (2 * ν * (‖f‖ ^ 2 + ‖g‖ ^ 2)) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by ring

lemma ApproxParallelogram.nonneg_of_nontrivial [Nontrivial E] {ν : ℝ}
    (h : ApproxParallelogram (fun x : E => ‖x‖) ν) : 0 ≤ ν := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hnx : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) _
  have hh := h x 0
  simp only [add_zero, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hh
  by_contra hn
  have hν : ν < 0 := lt_of_not_ge hn
  have hm : 2 * ν * ‖x‖ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hν) hnx
  nlinarith

/-- The real dual preserves the same constant, including degenerate spaces.
It can be applied repeatedly to pass to the bidual without reflexivity. -/
theorem ApproxParallelogram.dual {ν : ℝ}
    (h : ApproxParallelogram (fun x : E => ‖x‖) ν) :
    ApproxParallelogram (fun f : StrongDual ℝ E => ‖f‖) ν := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · intro f g
    have hf : f = 0 := Subsingleton.elim _ _
    have hg : g = 0 := Subsingleton.elim _ _
    simp only [hf, hg, add_zero, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      zero_add, mul_zero, le_refl]
  · exact ApproxParallelogram.dual_of_nonneg h.nonneg_of_nontrivial h

end ComplementedSubspace
