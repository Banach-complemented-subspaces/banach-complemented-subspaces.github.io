import ComplementedSubspace.ProjectionPerturbation
import ComplementedSubspace.FiniteFrame
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Counting-measure finite `ℓᵖ` bounds for the exact four-point frame projector. -/

noncomputable section
open scoped BigOperators ENNReal
open Matrix WithLp

namespace ComplementedSubspace

def finitePEnergy {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, |x i| ^ p

lemma finitePEnergy_nonneg {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) :
    0 ≤ finitePEnergy p x :=
  Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _

lemma finitePEnergy_smul {ι : Type*} [Fintype ι] (p c : ℝ) (x : ι → ℝ) :
    finitePEnergy p (c • x) = |c| ^ p * finitePEnergy p x := by
  simp only [finitePEnergy, Pi.smul_apply, smul_eq_mul, abs_mul,
    Real.mul_rpow (abs_nonneg c) (abs_nonneg _), Finset.mul_sum]

lemma norm_toLp_rpow {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p) (x : ι → ℝ) :
    ‖toLp (ENNReal.ofReal p) x‖ ^ p = finitePEnergy p x := by
  rw [PiLp.norm_eq_sum (by rw [ENNReal.toReal_ofReal hp.le]; exact hp)]
  simp only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs]
  change (finitePEnergy p x ^ (1 / p)) ^ p = finitePEnergy p x
  rw [← Real.rpow_mul (finitePEnergy_nonneg p x)]
  simp [finitePEnergy, hp.ne']

lemma abs_coordinate_le_one_of_sum_sq_le {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : (∑ i, x i ^ 2) ≤ 1) (i : ι) : |x i| ≤ 1 := by
  have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have := sq_abs (x i)
  nlinarith [abs_nonneg (x i)]

lemma fin_four_energy_lower {p : ℝ} (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (x : Fin 4 → ℝ) (hx : (∑ i, x i ^ 2) = 1) :
    (1 / 2 : ℝ) ≤ finitePEnergy p x := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := Finset.univ) (f := fun i => x i ^ 2)
    (by linarith : 1 ≤ p / 2) (fun i _ => sq_nonneg (x i))
  have heq (i : Fin 4) : (x i ^ 2) ^ (p / 2) = |x i| ^ p := by
    rw [← sq_abs, ← Real.rpow_natCast_mul (abs_nonneg (x i)) 2]
    congr 1
    ring
  simp only [hx, Real.one_rpow, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat,
    heq] at h
  have hconst : (4 : ℝ) ^ (p / 2 - 1) ≤ 2 := by
    calc
      (4 : ℝ) ^ (p / 2 - 1) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := by norm_num [← Real.sqrt_eq_rpow]
  have hsum := finitePEnergy_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hconst hsum
  change 1 ≤ 4 ^ (p / 2 - 1) * finitePEnergy p x at h
  linarith

lemma symmetric_idempotent_pythagorean {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (hQsym : Q.transpose = Q) (hQid : Q * Q = Q)
    (x : ι → ℝ) :
    (∑ i, (Q *ᵥ x) i ^ 2) + (∑ i, (x i - (Q *ᵥ x) i) ^ 2) =
      ∑ i, x i ^ 2 := by
  have hdot : x ⬝ᵥ (Q *ᵥ x) = (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) := by
    calc
      x ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ (Q.transpose *ᵥ (Q *ᵥ x)) := by
        rw [hQsym, Matrix.mulVec_mulVec, hQid]
      _ = (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) :=
        Matrix.dotProduct_transpose_mulVec Q x (Q *ᵥ x)
  have hexpand : (∑ i, (x i - (Q *ᵥ x) i) ^ 2) =
      (∑ i, x i ^ 2) - 2 * (x ⬝ᵥ (Q *ᵥ x)) + ∑ i, (Q *ᵥ x) i ^ 2 := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [dotProduct, ← pow_two] at hdot
  simp only [dotProduct] at hexpand
  linarith

lemma fin_four_projection_energy_bound {p : ℝ} (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (Q : Matrix (Fin 4) (Fin 4) ℝ) (hQsym : Q.transpose = Q) (hQid : Q * Q = Q)
    (x : Fin 4 → ℝ) (hx : (∑ i, x i ^ 2) = 1) :
    finitePEnergy p (Q *ᵥ x) ≤
      (1 + 18 * (p - 2) ^ 2) * finitePEnergy p x := by
  have horth := symmetric_idempotent_pythagorean Q hQsym hQid x
  have hsum0 : 0 ≤ ∑ i, (x i - (Q *ᵥ x) i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQx : (∑ i, (Q *ᵥ x) i ^ 2) ≤ 1 := by linarith
  have henergy := finite_projection_energy_bound hp x (Q *ᵥ x)
    (abs_coordinate_le_one_of_sum_sq_le x hx.le)
    (abs_coordinate_le_one_of_sum_sq_le (Q *ᵥ x) hQx) horth
  have hlower := fin_four_energy_lower hp hp3 x hx
  have heps := sq_nonneg (p - 2)
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at henergy
  change finitePEnergy p (Q *ᵥ x) ≤ finitePEnergy p x +
    9 * (p - 2) ^ 2 at henergy
  nlinarith

lemma fin_four_matrix_energy_bound {p : ℝ} (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (Q : Matrix (Fin 4) (Fin 4) ℝ) (hQsym : Q.transpose = Q) (hQid : Q * Q = Q)
    (x : Fin 4 → ℝ) :
    finitePEnergy p (Q *ᵥ x) ≤
      (1 + 18 * (p - 2) ^ 2) * finitePEnergy p x := by
  by_cases hx : x = 0
  · subst x
    simp [finitePEnergy, Real.zero_rpow (by linarith : p ≠ 0)]
  let X : EuclideanSpace ℝ (Fin 4) := toLp 2 x
  have hX : ‖X‖ ≠ 0 := by
    intro h
    have hzero : X = 0 := norm_eq_zero.mp h
    exact hx (congrArg ofLp hzero)
  let c : ℝ := ‖X‖⁻¹
  have hc : 0 < c := inv_pos.mpr (lt_of_le_of_ne (norm_nonneg X) (Ne.symm hX))
  have hn : (∑ i, (c • x) i ^ 2) = 1 := by
    have hn' : ‖c • X‖ ^ 2 = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      simp [c, hX]
    rw [EuclideanSpace.real_norm_sq_eq] at hn'
    simpa [X, PiLp.smul_apply, PiLp.toLp_apply] using hn'
  have h := fin_four_projection_energy_bound hp hp3 Q hQsym hQid (c • x) hn
  rw [Matrix.mulVec_smul, finitePEnergy_smul, finitePEnergy_smul] at h
  have hcp : 0 < |c| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr hc.ne') p
  apply (mul_le_mul_iff_right₀ hcp).mp
  nlinarith [h]

/-- The same matrix, acting on the genuine counting `ℓᵖ` coordinate norm. -/
def matrixPiLpLinear {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) (M : Matrix κ ι ℝ) :
    PiLp p (fun _ : ι => ℝ) →ₗ[ℝ] PiLp p (fun _ : κ => ℝ) :=
  (WithLp.linearEquiv p ℝ (κ → ℝ)).symm.toLinearMap.comp
    (M.mulVecLin.comp (WithLp.linearEquiv p ℝ (ι → ℝ)).toLinearMap)

def matrixPiLpCLM {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (M : Matrix κ ι ℝ) :
    PiLp p (fun _ : ι => ℝ) →L[ℝ] PiLp p (fun _ : κ => ℝ) :=
  (matrixPiLpLinear p M).toContinuousLinearMap

@[simp] lemma matrixPiLpCLM_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (M : Matrix κ ι ℝ)
    (x : PiLp p (fun _ : ι => ℝ)) :
    matrixPiLpCLM p M x = toLp p (M *ᵥ ofLp x) := rfl

lemma matrixPiLpCLM_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix μ κ ℝ) (B : Matrix κ ι ℝ) :
    (matrixPiLpCLM p A).comp (matrixPiLpCLM p B) = matrixPiLpCLM p (A * B) := by
  ext x i
  change (A *ᵥ (B *ᵥ ofLp x)) i = ((A * B) *ᵥ ofLp x) i
  rw [Matrix.mulVec_mulVec]

lemma matrixPiLpCLM_idempotent {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (Q : Matrix ι ι ℝ) (hQ : Q * Q = Q) :
    (matrixPiLpCLM p Q).comp (matrixPiLpCLM p Q) = matrixPiLpCLM p Q := by
  rw [matrixPiLpCLM_comp, hQ]

lemma matrixPiLpCLM_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Function.Injective (matrixPiLpCLM (ι := ι) (κ := κ) p) := by
  intro A B h
  apply Matrix.mulVec_injective
  funext x
  exact congrArg (fun F => ofLp (F (toLp p x))) h

@[simp] lemma matrixPiLpCLM_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    matrixPiLpCLM p (0 : Matrix κ ι ℝ) = 0 := by
  ext x i
  simp

@[simp] lemma matrixPiLpCLM_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    matrixPiLpCLM p (1 : Matrix ι ι ℝ) = ContinuousLinearMap.id ℝ _ := by
  ext x i
  simp

lemma matrixPiLpCLM_ne_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (M : Matrix κ ι ℝ) (hM : M ≠ 0) :
    matrixPiLpCLM p M ≠ 0 := by
  intro h
  exact hM (matrixPiLpCLM_injective p (h.trans (matrixPiLpCLM_zero p).symm))

lemma matrixPiLpCLM_norm_le_of_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p C : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) (hC : 0 ≤ C)
    (M : Matrix κ ι ℝ)
    (hM : ∀ x, finitePEnergy p (M *ᵥ x) ≤ C ^ p * finitePEnergy p x) :
    ‖matrixPiLpCLM (ENNReal.ofReal p) M‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (Real.rpow_le_rpow_iff (norm_nonneg _)
    (mul_nonneg hC (norm_nonneg x)) hp).mp
  rw [matrixPiLpCLM_apply, Real.mul_rpow hC (norm_nonneg x), norm_toLp_rpow hp]
  change finitePEnergy p (M *ᵥ ofLp x) ≤
    C ^ p * ‖toLp (ENNReal.ofReal p) (ofLp x)‖ ^ p
  rw [norm_toLp_rpow hp]
  exact hM (ofLp x)

theorem fin_four_matrixPiLpCLM_norm_le {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (Q : Matrix (Fin 4) (Fin 4) ℝ) (hQsym : Q.transpose = Q) (hQid : Q * Q = Q) :
    ‖matrixPiLpCLM (ENNReal.ofReal p) Q‖ ≤ 1 + 18 * (p - 2) ^ 2 := by
  have hC : 1 ≤ 1 + 18 * (p - 2) ^ 2 := by nlinarith [sq_nonneg (p - 2)]
  apply matrixPiLpCLM_norm_le_of_energy (by linarith : 0 < p) (by positivity) Q
  intro x
  exact (fin_four_matrix_energy_bound hp hp3 Q hQsym hQid x).trans
    (mul_le_mul_of_nonneg_right
      (Real.self_le_rpow_of_one_le hC (by linarith)) (finitePEnergy_nonneg p x))

theorem realFrameProjection_norm_le {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hp3 : p ≤ 3) :
    ‖matrixPiLpCLM (ENNReal.ofReal p) realFrameProjection‖ ≤
      1 + 18 * (p - 2) ^ 2 :=
  fin_four_matrixPiLpCLM_norm_le hp hp3 realFrameProjection
    realFrameProjection_transpose realFrameProjection_idempotent

end ComplementedSubspace
