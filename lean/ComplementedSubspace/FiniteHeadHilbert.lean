import ComplementedSubspace.LocalHilbertSum
import ComplementedSubspace.LpTwoUniformConvex
import ComplementedSubspace.FiniteLpGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual Hilbert norms on finite heads of dependent lp2 sums. -/
noncomputable section
open scoped BigOperators ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

/-- Finite lp2 sums preserve a common Hilbert comparison factor exactly. -/
theorem hasHilbertNormWithin_finite_lp_two {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {D : ℝ} (hD : 0 ≤ D) (hE : ∀ i, HasHilbertNormWithin (E i) D) :
    HasHilbertNormWithin (lp E 2) D := by
  classical
  choose q hq using fun i => (hE i).exists_model
  let G := PiLp 2 (fun i => (q i).Space)
  let A : lp E 2 →ₗ[ℝ] G :=
    { toFun := fun x => WithLp.toLp 2 (fun i => (q i).equivOfBounds D (hq i) (x i))
      map_add' := by intro x y; ext i; exact map_add ((q i).equivOfBounds D (hq i)) _ _
      map_smul' := by intro r x; ext i; exact map_smul ((q i).equivOfBounds D (hq i)) r _ }
  have hAnorm (x : lp E 2) : ‖A x‖ ^ 2 = ∑ i, (q i).q (x i) ^ 2 := by
    exact PiLp.norm_sq_eq_of_L2 _ (A x)
  have hxnorm (x : lp E 2) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
    simpa only [tsum_fintype] using (lp_two_hasSum_sq x).tsum_eq.symm
  apply hasHilbertNormWithin_of_hilbert_embedding (H := G) A
  intro x
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hAnorm, hxnorm]
    exact Finset.sum_le_sum fun i _ =>
      (sq_le_sq₀ (apply_nonneg (q i).q _) (norm_nonneg _)).mpr (hq i (x i)).1
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (norm_nonneg _))).mp
    rw [mul_pow, hAnorm, hxnorm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (apply_nonneg (q i).q _))).mpr
        (hq i (x i)).2

private theorem sum_rpow_le_rpow_sum_nonneg {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {r : ℝ} (hr : 1 ≤ r) :
    (∑ i ∈ s, f i ^ r) ≤ (∑ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow (by linarith : r ≠ 0)]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans
      (Real.add_rpow_le_rpow_add (hf i) (Finset.sum_nonneg fun j _ => hf j) hr)

theorem finitePiLp_norm_le_euclidean {ι : Type*} [Fintype ι]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p)
    (x : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ)) :
    ‖x‖ ≤ ‖(WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℝ ι)‖ := by
  have hp₀ : 0 < p := by linarith
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp₀).mp
  rw [piLp_norm_rpow_ofReal hp₀]
  have hs := sum_rpow_le_rpow_sum_nonneg Finset.univ (fun i => ‖x i‖ ^ 2)
    (fun i => sq_nonneg _) (by linarith : 1 ≤ p / 2)
  simp only [norm_sq_rpow_half] at hs
  convert hs using 1
  rw [← PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ)
    (WithLp.toLp 2 (WithLp.ofLp x)), norm_sq_rpow_half]

theorem euclidean_norm_le_card_scale_mul_finitePiLp {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p)
    (x : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ)) :
    ‖(WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℝ ι)‖ ≤
      (Fintype.card ι : ℝ) ^ (1 / 2 - 1 / p) * ‖x‖ := by
  have hp₀ : 0 < p := by linarith
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := Finset.univ) (f := fun i => ‖x i‖ ^ 2) (by linarith : 1 ≤ p / 2)
    (fun i _ => sq_nonneg _)
  simp only [Finset.card_univ, norm_sq_rpow_half] at hs
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hp₀).mp
  rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) (norm_nonneg x),
    ← Real.rpow_mul hN.le, piLp_norm_rpow_ofReal hp₀]
  have he : (1 / 2 - 1 / p) * p = p / 2 - 1 := by field_simp
  rw [he]
  convert hs using 1
  rw [← PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ)
    (WithLp.toLp 2 (WithLp.ofLp x)), norm_sq_rpow_half]

/-- The full scalar Lp block has an actual Hilbert norm with the full ambient
dimension factor, which also controls every one of its subspaces. -/
theorem finitePiLp_hasHilbertNormWithin {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) :
    HasHilbertNormWithin (PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ))
      ((Fintype.card ι : ℝ) ^ (1 / 2 - 1 / p)) := by
  let D := (Fintype.card ι : ℝ) ^ (1 / 2 - 1 / p)
  have hD : 0 < D := Real.rpow_pos_of_pos (by exact_mod_cast Fintype.card_pos) _
  let A : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι :=
    D⁻¹ • ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap.comp
      (WithLp.linearEquiv (ENNReal.ofReal p) ℝ (ι → ℝ)).toLinearMap)
  have hAnorm (x : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ)) :
      ‖A x‖ = D⁻¹ * ‖(WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℝ ι)‖ := by
    change ‖D⁻¹ • (WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℝ ι)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD)]
  apply hasHilbertNormWithin_of_hilbert_embedding A
  intro x
  rw [hAnorm]
  constructor
  · have h := euclidean_norm_le_card_scale_mul_finitePiLp hp x
    exact (mul_le_mul_of_nonneg_left h (inv_pos.mpr hD).le).trans_eq
      (by change D⁻¹ * (D * ‖x‖) = ‖x‖; rw [← mul_assoc, inv_mul_cancel₀ hD.ne', one_mul])
  · change ‖x‖ ≤ D * (D⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul]
    exact finitePiLp_norm_le_euclidean hp x

end ComplementedSubspace
