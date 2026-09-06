import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Lift
import Mathlib.Tactic.GCongr

/-! Elementary dimension-free finite-`ℓᵖ` geometry, over either real or complex scalars. -/

noncomputable section
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

lemma nonneg_rpow_add_upper {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 1 ≤ r) :
    (a + b) ^ r ≤ (2 : ℝ) ^ (r - 1) * (a ^ r + b ^ r) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hr

lemma norm_sq_rpow_half {E : Type*} [SeminormedAddCommGroup E] (x : E) (p : ℝ) :
    (‖x‖ ^ (2 : ℕ)) ^ (p / 2) = ‖x‖ ^ p := by
  rw [← Real.rpow_natCast_mul (norm_nonneg x) 2]
  congr 1
  ring

theorem scalar_clarkson {𝕜 : Type*} [RCLike 𝕜] {p : ℝ} (hp : 2 ≤ p) (a b : 𝕜) :
    ‖a + b‖ ^ p + ‖a - b‖ ^ p ≤
      (2 : ℝ) ^ (p - 1) * (‖a‖ ^ p + ‖b‖ ^ p) := by
  have hr : 1 ≤ p / 2 := by linarith
  have h1 := Real.add_rpow_le_rpow_add (sq_nonneg ‖a + b‖)
    (sq_nonneg ‖a - b‖) hr
  rw [norm_sq_rpow_half, norm_sq_rpow_half, parallelogram_law_with_norm 𝕜,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (add_nonneg (sq_nonneg ‖a‖) (sq_nonneg ‖b‖))] at h1
  have h2 := nonneg_rpow_add_upper (sq_nonneg ‖a‖) (sq_nonneg ‖b‖) hr
  rw [norm_sq_rpow_half, norm_sq_rpow_half] at h2
  calc
    ‖a + b‖ ^ p + ‖a - b‖ ^ p ≤
        2 ^ (p / 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ^ (p / 2) := h1
    _ ≤ 2 ^ (p / 2) * (2 ^ (p / 2 - 1) * (‖a‖ ^ p + ‖b‖ ^ p)) :=
      mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) _)
    _ = 2 ^ (p - 1) * (‖a‖ ^ p + ‖b‖ ^ p) := by
      rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

lemma piLp_norm_rpow_ofReal {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E]
    {p : ℝ} (hp : 0 < p) (x : PiLp (ENNReal.ofReal p) (fun _ : ι => E)) :
    ‖x‖ ^ p = ∑ i, ‖x i‖ ^ p := by
  rw [PiLp.norm_eq_sum (by rw [ENNReal.toReal_ofReal hp.le]; exact hp)]
  simp only [ENNReal.toReal_ofReal hp.le]
  rw [← Real.rpow_mul (Finset.sum_nonneg (fun i _ =>
    Real.rpow_nonneg (norm_nonneg (x i)) p))]
  simp [hp.ne']

theorem finitePiLp_clarkson {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p)
    (x y : PiLp (ENNReal.ofReal p) (fun _ : ι => 𝕜)) :
    ‖x + y‖ ^ p + ‖x - y‖ ^ p ≤
      (2 : ℝ) ^ (p - 1) * (‖x‖ ^ p + ‖y‖ ^ p) := by
  have hp0 : 0 < p := by linarith
  simp only [piLp_norm_rpow_ofReal hp0, PiLp.add_apply, PiLp.sub_apply,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => scalar_clarkson hp (x i) (y i)

lemma nonneg_two_energy_compare {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 2 ≤ p) :
    a ^ (2 : ℕ) + b ^ (2 : ℕ) ≤
      (2 : ℝ) ^ (1 - 2 / p) * (a ^ p + b ^ p) ^ (2 / p) := by
  have hp0 : 0 < p := by linarith
  have h := nonneg_rpow_add_upper (sq_nonneg a) (sq_nonneg b) (by linarith : 1 ≤ p / 2)
  have heq (c : ℝ) (hc : 0 ≤ c) : (c ^ (2 : ℕ)) ^ (p / 2) = c ^ p := by
    rw [← Real.rpow_natCast_mul hc 2]
    congr 1
    ring
  rw [heq a ha, heq b hb] at h
  have ht := Real.rpow_le_rpow (Real.rpow_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b)) _)
    h (by positivity : 0 ≤ 2 / p)
  rw [← Real.rpow_mul (add_nonneg (sq_nonneg a) (sq_nonneg b)),
    Real.mul_rpow (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg (Real.rpow_nonneg ha p) (Real.rpow_nonneg hb p)),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at ht
  have he1 : p / 2 * (2 / p) = 1 := by field_simp [hp0.ne']
  have he2 : (p / 2 - 1) * (2 / p) = 1 - 2 / p := by field_simp [hp0.ne']
  simpa only [he1, he2, Real.rpow_one] using ht

theorem finitePiLp_parallelogram_le {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p)
    (x y : PiLp (ENNReal.ofReal p) (fun _ : ι => 𝕜)) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 ≤
      2 * (2 : ℝ) ^ (2 - 4 / p) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hp0 : 0 < p := by linarith
  have h0 := nonneg_two_energy_compare (norm_nonneg (x + y)) (norm_nonneg (x - y)) hp
  have hc := finitePiLp_clarkson hp x y
  have hc' := Real.rpow_le_rpow
    (add_nonneg (Real.rpow_nonneg (norm_nonneg (x + y)) p)
      (Real.rpow_nonneg (norm_nonneg (x - y)) p)) hc (by positivity : 0 ≤ 2 / p)
  have hnorm : (‖x‖ ^ p + ‖y‖ ^ p) ^ (2 / p) ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    simpa only [norm_sq_rpow_half, one_div_div] using Real.rpow_add_rpow_le_add
      (sq_nonneg ‖x‖) (sq_nonneg ‖y‖) (by linarith : 1 ≤ p / 2)
  rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _)
    (add_nonneg (Real.rpow_nonneg (norm_nonneg x) p)
      (Real.rpow_nonneg (norm_nonneg y) p)),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hc'
  calc
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 ≤
        2 ^ (1 - 2 / p) * (‖x + y‖ ^ p + ‖x - y‖ ^ p) ^ (2 / p) := h0
    _ ≤ 2 ^ (1 - 2 / p) *
        (2 ^ ((p - 1) * (2 / p)) * (‖x‖ ^ p + ‖y‖ ^ p) ^ (2 / p)) :=
      mul_le_mul_of_nonneg_left hc' (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 2 ^ (1 - 2 / p) *
        (2 ^ ((p - 1) * (2 / p)) * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by
      gcongr
    _ = 2 * 2 ^ (2 - 4 / p) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have he : 1 - 2 / p + (p - 1) * (2 / p) = 1 + (2 - 4 / p) := by
        field_simp [hp0.ne']
        ring
      rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]

/-- A common modulus obtained from Clarkson for all exponents in `[2,3]`.
The estimate is stated for the sum, so the midpoint modulus is `ε^3 / 24`. -/
theorem clarkson_uniform_modulus {E : Type*} [NormedAddCommGroup E]
    {p ε : ℝ} (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (hclark : ∀ x y : E, ‖x + y‖ ^ p + ‖x - y‖ ^ p ≤
      (2 : ℝ) ^ (p - 1) * (‖x‖ ^ p + ‖y‖ ^ p))
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hε : 0 ≤ ε) (hxy : ε ≤ ‖x - y‖) :
    ‖x + y‖ ≤ 2 - ε ^ (3 : ℕ) / 12 := by
  have hp0 : 0 ≤ p := by linarith
  have hxpow : ‖x‖ ^ p ≤ 1 := Real.rpow_le_one (norm_nonneg x) hx hp0
  have hypow : ‖y‖ ^ p ≤ 1 := Real.rpow_le_one (norm_nonneg y) hy hp0
  have hcap : ‖x + y‖ ^ p + ‖x - y‖ ^ p ≤ (2 : ℝ) ^ p := by
    refine (hclark x y).trans ?_
    calc
      2 ^ (p - 1) * (‖x‖ ^ p + ‖y‖ ^ p) ≤ 2 ^ (p - 1) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ p := by
        calc
          (2 : ℝ) ^ (p - 1) * 2 = 2 ^ (p - 1) * 2 ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = 2 ^ ((p - 1) + 1) := (Real.rpow_add (by norm_num : (0 : ℝ) < 2) (p - 1) 1).symm
          _ = 2 ^ p := by congr 1; ring
  let m : ℝ := ‖x + y‖ / 2
  let d : ℝ := ‖x - y‖ / 2
  have hm0 : 0 ≤ m := by positivity
  have hd0 : 0 ≤ d := by positivity
  have hm1 : m ≤ 1 := by
    dsimp [m]
    linarith [norm_add_le x y]
  have hd1 : d ≤ 1 := by
    dsimp [d]
    linarith [norm_sub_le x y]
  have hscale : m ^ p + d ^ p ≤ 1 := by
    have heq : m ^ p + d ^ p =
        (‖x + y‖ ^ p + ‖x - y‖ ^ p) / (2 : ℝ) ^ p := by
      dsimp [m, d]
      rw [Real.div_rpow (norm_nonneg _) (by norm_num),
        Real.div_rpow (norm_nonneg _) (by norm_num), add_div]
    rw [heq]
    exact (div_le_one₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p)).mpr hcap
  have hm3 : m ^ (3 : ℕ) ≤ m ^ p := by
    rw [← Real.rpow_natCast m 3]
    exact Real.rpow_le_rpow_of_exponent_ge' hm0 hm1 hp0 hp3
  have hd3 : d ^ (3 : ℕ) ≤ d ^ p := by
    rw [← Real.rpow_natCast d 3]
    exact Real.rpow_le_rpow_of_exponent_ge' hd0 hd1 hp0 hp3
  have heps3 : (ε / 2) ^ (3 : ℕ) ≤ d ^ (3 : ℕ) := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [d]
    linarith
  have htangent : 3 * m - 2 ≤ m ^ (3 : ℕ) := by
    nlinarith only [mul_nonneg (sq_nonneg (m - 1)) (by linarith only [hm0] : 0 ≤ m + 2)]
  have hmdef : 2 * m = ‖x + y‖ := by dsimp [m]; ring
  nlinarith only [hm3, hd3, heps3, hscale, htangent, hmdef]

theorem finitePiLp_uniform_modulus {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
    {p ε : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (x y : PiLp (ENNReal.ofReal p) (fun _ : ι => 𝕜))
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hε : 0 ≤ ε) (hxy : ε ≤ ‖x - y‖) :
    ‖x + y‖ ≤ 2 - ε ^ (3 : ℕ) / 12 :=
  clarkson_uniform_modulus (E := PiLp (ENNReal.ofReal p) (fun _ : ι => 𝕜))
    (p := p) hp hp3 (fun a b => finitePiLp_clarkson (ι := ι) (𝕜 := 𝕜) hp a b)
    x y hx hy hε hxy

theorem finitePiLp_uniformConvexSpace {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) (hp3 : p ≤ 3) :
    UniformConvexSpace (PiLp (ENNReal.ofReal p) (fun _ : ι => 𝕜)) := by
  constructor
  intro ε hε
  refine ⟨ε ^ (3 : ℕ) / 12, by positivity, ?_⟩
  intro x hx y hy hxy
  exact finitePiLp_uniform_modulus hp hp3 x y hx.le hy.le hε.le hxy

theorem finitePiLp_parallelogram_constant_ge_one {p : ℝ} (hp : 2 ≤ p) :
    1 ≤ (2 : ℝ) ^ (2 - 4 / p) := by
  apply Real.one_le_rpow (by norm_num)
  have hp0 : 0 < p := by linarith
  have h : 4 / p ≤ (2 : ℝ) := (div_le_iff₀ hp0).mpr (by linarith)
  linarith

theorem finitePiLp_parallelogram_constant_tendsto :
    Filter.Tendsto (fun p : ℝ => (2 : ℝ) ^ (2 - 4 / p)) (nhds 2) (nhds 1) := by
  have hinner : ContinuousAt (fun p : ℝ => 2 - 4 / p) 2 :=
    continuousAt_const.sub (continuousAt_const.div continuousAt_id (by norm_num))
  have h := (Real.continuousAt_const_rpow (a := 2) (b := 2 - 4 / (2 : ℝ))
    (by norm_num)).comp (f := fun p : ℝ => 2 - 4 / p) (x := (2 : ℝ)) hinner
  have heval : (2 : ℝ) ^ (2 - 4 / (2 : ℝ)) = 1 := by norm_num
  simpa only [Function.comp_def, heval] using h.tendsto

end ComplementedSubspace
