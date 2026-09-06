import ComplementedSubspace.ComplexProjectionEnergy
import ComplementedSubspace.FiniteLpGeometry

/-! The complex counting-Lp realization of the same finite real orthogonal
projection. Radial energy comparison gives the quadratic constant18. -/
noncomputable section
open scoped BigOperators ENNReal
open Matrix WithLp
namespace ComplementedSubspace

theorem complex_norm_toLp_rpow {ι : Type*} [Fintype ι] {p : ℝ}
    (hp : 0 < p) (x : ι → ℂ) :
    ‖toLp (ENNReal.ofReal p) x‖ ^ p = complexPEnergy p x :=
  piLp_norm_rpow_ofReal hp (toLp (ENNReal.ofReal p) x)

theorem fin_four_complex_matrix_energy_bound {p : ℝ} (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (Q : Matrix (Fin 4) (Fin 4) ℝ) (hQsym : Q.transpose = Q) (hQid : Q * Q = Q)
    (x : Fin 4 → ℂ) :
    complexPEnergy p (complexifyMatrix Q *ᵥ x) ≤
      (1 + 18 * (p - 2) ^ 2) * complexPEnergy p x := by
  by_cases hx : x = 0
  · subst x
    simp [complexPEnergy, Real.zero_rpow (by linarith : p ≠ 0)]
  let X : EuclideanSpace ℂ (Fin 4) := toLp 2 x
  have hX : ‖X‖ ≠ 0 := by
    intro h
    have hzero : X = 0 := norm_eq_zero.mp h
    exact hx (congrArg ofLp hzero)
  let c : ℝ := ‖X‖⁻¹
  have hc : 0 < c := inv_pos.mpr (lt_of_le_of_ne (norm_nonneg X) (Ne.symm hX))
  have hn : (∑ i, ‖(c • x) i‖ ^ 2) = 1 := by
    have hn' : ‖c • X‖ ^ 2 = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      simp [c, hX]
    rw [EuclideanSpace.norm_sq_eq] at hn'
    simpa [X, PiLp.smul_apply, PiLp.toLp_apply] using hn'
  have h := fin_four_complex_projection_energy_bound hp hp3 Q hQsym hQid (c • x) hn
  rw [Matrix.mulVec_smul, complexPEnergy_real_smul, complexPEnergy_real_smul] at h
  have hcp : 0 < |c| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr hc.ne') p
  apply (mul_le_mul_iff_right₀ hcp).mp
  nlinarith [h]
def complexMatrixPiLpLinear {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) (M : Matrix κ ι ℂ) :
    PiLp p (fun _ : ι => ℂ) →ₗ[ℂ] PiLp p (fun _ : κ => ℂ) :=
  (WithLp.linearEquiv p ℂ (κ → ℂ)).symm.toLinearMap.comp
    (M.mulVecLin.comp (WithLp.linearEquiv p ℂ (ι → ℂ)).toLinearMap)

def complexMatrixPiLpCLM {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (M : Matrix κ ι ℂ) :
    PiLp p (fun _ : ι => ℂ) →L[ℂ] PiLp p (fun _ : κ => ℂ) :=
  (complexMatrixPiLpLinear p M).toContinuousLinearMap

@[simp] lemma complexMatrixPiLpCLM_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (M : Matrix κ ι ℂ)
    (x : PiLp p (fun _ : ι => ℂ)) :
    complexMatrixPiLpCLM p M x = toLp p (M *ᵥ ofLp x) := rfl

lemma complexMatrixPiLpCLM_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix μ κ ℂ) (B : Matrix κ ι ℂ) :
    (complexMatrixPiLpCLM p A).comp (complexMatrixPiLpCLM p B) = complexMatrixPiLpCLM p (A * B) := by
  ext x i
  change (A *ᵥ (B *ᵥ ofLp x)) i = ((A * B) *ᵥ ofLp x) i
  rw [Matrix.mulVec_mulVec]

lemma complexMatrixPiLpCLM_idempotent {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (Q : Matrix ι ι ℂ) (hQ : Q * Q = Q) :
    (complexMatrixPiLpCLM p Q).comp (complexMatrixPiLpCLM p Q) = complexMatrixPiLpCLM p Q := by
  rw [complexMatrixPiLpCLM_comp, hQ]

lemma complexMatrixPiLpCLM_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Function.Injective (complexMatrixPiLpCLM (ι := ι) (κ := κ) p) := by
  intro A B h
  apply Matrix.mulVec_injective
  funext x
  exact congrArg (fun F => ofLp (F (toLp p x))) h

@[simp] lemma complexMatrixPiLpCLM_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    complexMatrixPiLpCLM p (0 : Matrix κ ι ℂ) = 0 := by
  ext x i
  simp

@[simp] lemma complexMatrixPiLpCLM_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    complexMatrixPiLpCLM p (1 : Matrix ι ι ℂ) = ContinuousLinearMap.id ℂ _ := by
  ext x i
  simp

lemma complexMatrixPiLpCLM_ne_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (M : Matrix κ ι ℂ) (hM : M ≠ 0) :
    complexMatrixPiLpCLM p M ≠ 0 := by
  intro h
  exact hM (complexMatrixPiLpCLM_injective p (h.trans (complexMatrixPiLpCLM_zero p).symm))

lemma complexMatrixPiLpCLM_norm_le_of_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p C : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) (hC : 0 ≤ C)
    (M : Matrix κ ι ℂ)
    (hM : ∀ x, complexPEnergy p (M *ᵥ x) ≤ C ^ p * complexPEnergy p x) :
    ‖complexMatrixPiLpCLM (ENNReal.ofReal p) M‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (Real.rpow_le_rpow_iff (norm_nonneg _)
    (mul_nonneg hC (norm_nonneg x)) hp).mp
  rw [complexMatrixPiLpCLM_apply, Real.mul_rpow hC (norm_nonneg x), complex_norm_toLp_rpow hp]
  change complexPEnergy p (M *ᵥ ofLp x) ≤
    C ^ p * ‖toLp (ENNReal.ofReal p) (ofLp x)‖ ^ p
  rw [complex_norm_toLp_rpow hp]
  exact hM (ofLp x)

theorem fin_four_complexMatrixPiLpCLM_norm_le {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (Q : Matrix (Fin 4) (Fin 4) ℝ) (hQsym : Q.transpose = Q) (hQid : Q * Q = Q) :
    ‖complexMatrixPiLpCLM (ENNReal.ofReal p) (complexifyMatrix Q)‖ ≤
      1 + 18 * (p - 2) ^ 2 := by
  have hC : 1 ≤ 1 + 18 * (p - 2) ^ 2 := by nlinarith [sq_nonneg (p - 2)]
  apply complexMatrixPiLpCLM_norm_le_of_energy (by linarith : 0 < p) (by positivity)
  intro x
  exact (fin_four_complex_matrix_energy_bound hp hp3 Q hQsym hQid x).trans
    (mul_le_mul_of_nonneg_right
      (Real.self_le_rpow_of_one_le hC (by linarith)) (complexPEnergy_nonneg p x))

theorem complexifyMatrix_mul {ι κ μ : Type*} [Fintype κ]
    (A : Matrix ι κ ℝ) (B : Matrix κ μ ℝ) :
    complexifyMatrix (A * B) = complexifyMatrix A * complexifyMatrix B := by
  ext i j
  simp [complexifyMatrix, Matrix.mul_apply]

theorem complexifyMatrix_idempotent {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (hQ : Q * Q = Q) :
    complexifyMatrix Q * complexifyMatrix Q = complexifyMatrix Q := by
  rw [← complexifyMatrix_mul, hQ]

def complexFrameProjection : Matrix (Fin 4) (Fin 4) ℂ :=
  complexifyMatrix realFrameProjection

theorem complexFrameProjection_idempotent :
    complexFrameProjection * complexFrameProjection = complexFrameProjection :=
  complexifyMatrix_idempotent realFrameProjection realFrameProjection_idempotent

theorem complexFrameProjection_clm_idempotent (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (complexMatrixPiLpCLM p complexFrameProjection).comp
      (complexMatrixPiLpCLM p complexFrameProjection) =
        complexMatrixPiLpCLM p complexFrameProjection :=
  complexMatrixPiLpCLM_idempotent p _ complexFrameProjection_idempotent

theorem complexFrameProjection_norm_le {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hp3 : p ≤ 3) :
    ‖complexMatrixPiLpCLM (ENNReal.ofReal p) complexFrameProjection‖ ≤
      1 + 18 * (p - 2) ^ 2 :=
  fin_four_complexMatrixPiLpCLM_norm_le hp hp3 realFrameProjection
    realFrameProjection_transpose realFrameProjection_idempotent

end ComplementedSubspace
