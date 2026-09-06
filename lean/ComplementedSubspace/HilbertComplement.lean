import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An elementary bound for complementary Hilbert-space projections

The proof uses a vector identity, without spectral theory or a general
projection-complement theorem. Completeness and finite dimension are unnecessary.
-/

noncomputable section

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The algebraic identity underlying the complement estimate. -/
lemma hilbert_complement_vector_identity (y z : E) :
    ‖z‖ ^ 2 * ‖y‖ ^ 2 * ‖y + z‖ ^ 2 -
        ‖‖z‖ ^ 2 • y - inner ℝ y z • z‖ ^ 2 =
      ‖z‖ ^ 2 * (‖y‖ ^ 2 + inner ℝ y z) ^ 2 := by
  rw [norm_add_sq_real,
    ← real_inner_self_eq_norm_sq (‖z‖ ^ 2 • y - inner ℝ y z • z)]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm z y]
  ring

/-- A norm bound for the test vector in the elementary projection argument. -/
lemma hilbert_complement_vector_norm_le (y z : E) :
    ‖‖z‖ ^ 2 • y - inner ℝ y z • z‖ ≤ ‖z‖ * ‖y‖ * ‖y + z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hi := hilbert_complement_vector_identity y z
  have hp : 0 ≤ ‖z‖ ^ 2 * (‖y‖ ^ 2 + inner ℝ y z) ^ 2 := by positivity
  nlinarith

/-- Every nonzero bounded idempotent has norm at least one. -/
lemma one_le_norm_nonzero_idempotent (P : E →L[ℝ] E)
    (hPP : P.comp P = P) (hP : P ≠ 0) : 1 ≤ ‖P‖ := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, P x ≠ 0 := by
    by_contra h
    apply hP
    ext x
    by_contra hn
    exact h ⟨x, hn⟩
  have hfix : P (P x) = P x := by
    simpa only [ContinuousLinearMap.comp_apply] using congrArg (fun T => T x) hPP
  have h := P.le_opNorm (P x)
  rw [hfix] at h
  exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hx)).mp (by simpa [mul_comm] using h)

/-- The complement of a nonzero projection on a real Hilbert space has no
larger norm. The proof does not need completeness or finite dimension. -/
theorem hilbert_norm_complement_le (P : E →L[ℝ] E)
    (hPP : P.comp P = P) (hP : P ≠ 0) :
    ‖ContinuousLinearMap.id ℝ E - P‖ ≤ ‖P‖ := by
  have h1 := one_le_norm_nonzero_idempotent P hPP hP
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖x - P x‖ ≤ ‖P‖ * ‖x‖
  let y := P x
  let z := x - P x
  have hyz : y + z = x := by
    dsimp [y, z]
    simpa only [add_sub_assoc] using add_sub_cancel_left (P x) x
  have hPy : P y = y := by
    simpa only [y, ContinuousLinearMap.comp_apply] using congrArg (fun T => T x) hPP
  have hPz : P z = 0 := by
    dsimp [z]
    rw [map_sub]
    change P x - P y = 0
    rw [hPy]
    exact sub_self _
  change ‖z‖ ≤ ‖P‖ * ‖x‖
  by_cases hy : y = 0
  · have hz : z = x := by simpa only [hy, zero_add] using hyz
    rw [hz]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
  by_cases hz : z = 0
  · rw [hz, norm_zero]
    positivity
  let w := ‖z‖ ^ 2 • y - inner ℝ y z • z
  have hPw : P w = ‖z‖ ^ 2 • y := by
    simp only [w, map_sub, map_smul, hPy, hPz, smul_zero, sub_zero]
  have hw : ‖w‖ ≤ ‖z‖ * ‖y‖ * ‖x‖ := by
    simpa only [w, hyz] using hilbert_complement_vector_norm_le y z
  have hb : ‖z‖ ^ 2 * ‖y‖ ≤ ‖P‖ * (‖z‖ * ‖y‖ * ‖x‖) := by
    have hop := P.le_opNorm w
    rw [hPw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hop
    exact hop.trans (mul_le_mul_of_nonneg_left hw (norm_nonneg P))
  have hc : (‖z‖ * ‖y‖) * ‖z‖ ≤ (‖z‖ * ‖y‖) * (‖P‖ * ‖x‖) := by
    nlinarith [hb]
  exact (mul_le_mul_iff_right₀
    (mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hy))).mp hc

/-- A nontrivial Hilbert-space projection and its nonzero complement have
equal operator norms. -/
theorem hilbert_norm_complement_eq (P : E →L[ℝ] E)
    (hPP : P.comp P = P) (hP : P ≠ 0)
    (hQ : ContinuousLinearMap.id ℝ E - P ≠ 0) :
    ‖ContinuousLinearMap.id ℝ E - P‖ = ‖P‖ := by
  apply le_antisymm (hilbert_norm_complement_le P hPP hP)
  have hfix (x : E) : P (P x) = P x := by
    simpa only [ContinuousLinearMap.comp_apply] using congrArg (fun T => T x) hPP
  have hQQ : (ContinuousLinearMap.id ℝ E - P).comp
      (ContinuousLinearMap.id ℝ E - P) = ContinuousLinearMap.id ℝ E - P := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, map_sub, hfix, sub_self, sub_zero]
  simpa only [sub_sub_cancel] using
    hilbert_norm_complement_le (ContinuousLinearMap.id ℝ E - P) hQQ hQ

end ComplementedSubspace
