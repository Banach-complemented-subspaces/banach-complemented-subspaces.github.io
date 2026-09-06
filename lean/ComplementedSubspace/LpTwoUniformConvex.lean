import ComplementedSubspace.FiniteLpGeometry
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Uniform convexity of dependent `ℓ²` sums with a common cubic modulus. -/

noncomputable section
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

def HasCubicSumModulus (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ ε : ℝ, 0 ≤ ε → ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
    ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - ε ^ (3 : ℕ) / 12

private lemma scalar_deficit_of_le {a b s d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hab : a ≤ b) (hsum : s ≤ a + b) (hmod : s ≤ (2 - 2 * d) * b) :
    d ^ 2 * (a ^ 2 + b ^ 2) ≤ 2 * (a ^ 2 + b ^ 2) - s ^ 2 := by
  have hr0 : 0 ≤ a + b := add_nonneg ha hb
  have hrE : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith [mul_nonneg ha hb]
  have hs2 : s ^ 2 ≤ (a + b) ^ 2 := (sq_le_sq₀ hs hr0).mpr hsum
  have hdE := mul_le_mul_of_nonneg_left hrE (sq_nonneg d)
  by_cases hbal : d * (a + b) ≤ b - a
  · have hbal2 := (sq_le_sq₀ (mul_nonneg hd hr0) (sub_nonneg.mpr hab)).mpr hbal
    nlinarith only [hdE, hbal2, hs2]
  · have hb' : 2 * b ≤ (1 + d) * (a + b) := by linarith
    have hm := mul_le_mul_of_nonneg_left hb' (sub_nonneg.mpr hd1)
    have hS : s ≤ (1 - d ^ 2) * (a + b) := by nlinarith only [hmod, hm]
    have hk : 0 ≤ 1 - d ^ 2 := by nlinarith only [hd, hd1]
    have hS2 := mul_le_mul hS hsum hs (mul_nonneg hk hr0)
    nlinarith only [hdE, hS2, sq_nonneg (a - b)]

private lemma scalar_deficit {a b s d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hsum : s ≤ a + b) (hmod : s ≤ (2 - 2 * d) * max a b) :
    d ^ 2 * (a ^ 2 + b ^ 2) ≤ 2 * (a ^ 2 + b ^ 2) - s ^ 2 := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab] at hmod
    exact scalar_deficit_of_le ha hb hs hd hd1 hab hsum hmod
  · rw [max_eq_left hba] at hmod
    simpa only [add_comm] using scalar_deficit_of_le hb ha hs hd hd1 hba
      (by simpa only [add_comm] using hsum) hmod

theorem cubic_modulus_sq_deficit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : HasCubicSumModulus E) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (x y : E) (hlarge : η * (‖x‖ + ‖y‖) ≤ ‖x - y‖) :
    (η ^ (3 : ℕ) / 24) ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤
      2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) - ‖x + y‖ ^ 2 := by
  let m : ℝ := max ‖x‖ ‖y‖
  have hm0 : 0 ≤ m := (norm_nonneg x).trans (le_max_left _ _)
  by_cases hm : m = 0
  · have hx : x = 0 := norm_eq_zero.mp (le_antisymm (by simpa [m, hm] using le_max_left ‖x‖ ‖y‖) (norm_nonneg x))
    have hy : y = 0 := norm_eq_zero.mp (le_antisymm (by simpa [m, hm] using le_max_right ‖x‖ ‖y‖) (norm_nonneg y))
    simp [hx, hy]
  have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
  have hxm : ‖m⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hmpos]
    have h := mul_le_mul_of_nonneg_left (le_max_left ‖x‖ ‖y‖) (inv_nonneg.mpr hm0)
    simpa only [show max ‖x‖ ‖y‖ = m from rfl, inv_mul_cancel₀ hm] using h
  have hym : ‖m⁻¹ • y‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hmpos]
    have h := mul_le_mul_of_nonneg_left (le_max_right ‖x‖ ‖y‖) (inv_nonneg.mpr hm0)
    simpa only [show max ‖x‖ ‖y‖ = m from rfl, inv_mul_cancel₀ hm] using h
  have hmle : m ≤ ‖x‖ + ‖y‖ := max_le (by linarith [norm_nonneg y]) (by linarith [norm_nonneg x])
  have hdist : η ≤ ‖m⁻¹ • x - m⁻¹ • y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hmpos]
    have hmul : η * m ≤ ‖x - y‖ :=
      (mul_le_mul_of_nonneg_left hmle hη).trans hlarge
    calc
      η = m⁻¹ * (η * m) := by field_simp
      _ ≤ m⁻¹ * ‖x - y‖ := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hm0)
  have h := hE η hη (m⁻¹ • x) (m⁻¹ • y) hxm hym hdist
  rw [← smul_add, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hmpos] at h
  have hmback := mul_le_mul_of_nonneg_left h hm0
  rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul] at hmback
  have hcube : η ^ (3 : ℕ) ≤ 1 := by simpa using pow_le_pow_left₀ hη hη1 3
  apply scalar_deficit (norm_nonneg x) (norm_nonneg y) (norm_nonneg (x + y))
    (by positivity) (by linarith) (norm_add_le x y)
  dsimp [m] at hmback
  nlinarith only [hmback]

theorem cubic_modulus_energy_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : HasCubicSumModulus E) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (x y : E) :
    (η ^ (3 : ℕ) / 24) ^ 2 * ‖x - y‖ ^ 2 ≤
      2 * (η ^ (3 : ℕ) / 24) ^ 2 * η ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) +
      2 * (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) - ‖x + y‖ ^ 2) := by
  let g : ℝ := (η ^ (3 : ℕ) / 24) ^ 2
  have hg : 0 ≤ g := sq_nonneg _
  have hsum2 : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hplus : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
    ((sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr
      (norm_add_le x y)).trans hsum2
  have hminus : ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
    ((sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr
      (norm_sub_le x y)).trans hsum2
  change g * ‖x - y‖ ^ 2 ≤ 2 * g * η ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + _
  by_cases hsmall : ‖x - y‖ ≤ η * (‖x‖ + ‖y‖)
  · have hc2 := (sq_le_sq₀ (norm_nonneg (x - y))
      (mul_nonneg hη (add_nonneg (norm_nonneg x) (norm_nonneg y)))).mpr hsmall
    have hc3 := mul_le_mul_of_nonneg_left hsum2 (sq_nonneg η)
    have hc4 : ‖x - y‖ ^ 2 ≤ 2 * η ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      nlinarith only [hc2, hc3]
    have h := mul_le_mul_of_nonneg_left hc4 hg
    nlinarith only [h, hplus]
  · have hd := cubic_modulus_sq_deficit hE hη hη1 x y (le_of_lt (lt_of_not_ge hsmall))
    change g * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ _ at hd
    have h := mul_le_mul_of_nonneg_left hminus hg
    have hrest : 0 ≤ 2 * g * η ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by positivity
    nlinarith only [h, hd, hrest]

theorem lp_two_hasSum_sq {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (x : lp E 2) :
    HasSum (fun i => ‖x i‖ ^ (2 : ℕ)) (‖x‖ ^ (2 : ℕ)) := by
  simpa using lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x

theorem lp_two_cubic_energy_bound {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (hE : ∀ i, HasCubicSumModulus (E i)) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (x y : lp E 2) :
    (η ^ (3 : ℕ) / 24) ^ 2 * ‖x - y‖ ^ 2 ≤
      2 * (η ^ (3 : ℕ) / 24) ^ 2 * η ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) +
      2 * (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) - ‖x + y‖ ^ 2) := by
  have hx := lp_two_hasSum_sq x
  have hy := lp_two_hasSum_sq y
  have hplus := lp_two_hasSum_sq (x + y)
  have hminus := lp_two_hasSum_sq (x - y)
  have hleft := hminus.mul_left ((η ^ (3 : ℕ) / 24) ^ 2)
  have hright := ((hx.add hy).mul_left (2 * (η ^ (3 : ℕ) / 24) ^ 2 * η ^ 2)).add
    ((((hx.add hy).mul_left 2).sub hplus).mul_left 2)
  apply hasSum_le _ hleft hright
  intro i
  simpa only [lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply] using
    cubic_modulus_energy_bound (hE i) hη hη1 (x i) (y i)

theorem lp_two_uniformConvexSpace_of_cubicModulus {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (hE : ∀ i, HasCubicSumModulus (E i)) : UniformConvexSpace (lp E 2) := by
  constructor
  intro ε hε
  by_cases hε2 : ε ≤ 2
  · let η : ℝ := ε / 4
    let g : ℝ := (η ^ (3 : ℕ) / 24) ^ 2
    have hη : 0 < η := by dsimp [η]; positivity
    have hη1 : η ≤ 1 := by dsimp [η]; linarith
    have hg : 0 < g := by dsimp [g]; positivity
    refine ⟨g * ε ^ 2 / 32, by positivity, ?_⟩
    intro x hx y hy hxy
    have h := lp_two_cubic_energy_bound hE hη.le hη1 x y
    change g * ‖x - y‖ ^ 2 ≤ 2 * g * η ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) +
      2 * (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) - ‖x + y‖ ^ 2) at h
    rw [hx, hy] at h
    have hdist : ε ^ 2 ≤ ‖x - y‖ ^ 2 :=
      (sq_le_sq₀ hε.le (norm_nonneg _)).mpr hxy
    have hdistg := mul_le_mul_of_nonneg_left hdist hg.le
    have hηeq : 16 * η ^ 2 = ε ^ 2 := by dsimp [η]; ring
    have hηeqg := congrArg (fun r : ℝ => g * r) hηeq
    have hepsg : 0 ≤ g * ε ^ 2 := by positivity
    nlinarith only [h, hdistg, hηeqg, hepsg, sq_nonneg (‖x + y‖ - 2)]
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx y hy hxy
    have h := norm_sub_le x y
    rw [hx, hy] at h
    exfalso
    linarith

end ComplementedSubspace
