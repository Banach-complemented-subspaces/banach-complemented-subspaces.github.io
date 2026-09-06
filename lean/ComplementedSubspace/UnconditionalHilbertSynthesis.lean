import ComplementedSubspace.FiniteBasisTraceBound
import ComplementedSubspace.FiniteHilbertAverage
import ComplementedSubspace.DPRtoGL
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Hilbert synthesis bounds from an unconditional basis

Finite sign averaging converts a normalized unconditional basis into an
isomorphism with Euclidean coordinates, with distortion bounded using the
comparison between its Banach and Hilbert norms.
-/

noncomputable section
open scoped BigOperators ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem finiteAverage_basis_sign_norm_sq {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (T : E →ₗ[ℝ] H) (a : Fin m → ℝ) :
    finiteAverage (fun s =>
      ‖T (b.equivFun.symm (fun i => realSignVector m s i * a i))‖ ^ 2) =
      ∑ i, a i ^ 2 * ‖T (b i)‖ ^ 2 := by
  classical
  let A := T.comp b.equivFun.symm.toLinearMap
  change finiteAverage (fun s => ‖A (fun i => realSignVector m s i * a i)‖ ^ 2) = _
  rw [finiteAverage_linearMap_norm_sq]
  have hcov (i j : Fin m) :
      finiteAverage (fun s => (realSignVector m s i * a i) *
        (realSignVector m s j * a j)) =
      (a i * a j) * (if i = j then 1 else 0) := by
    simp_rw [show ∀ s, (realSignVector m s i * a i) *
      (realSignVector m s j * a j) =
      (a i * a j) * (realSignVector m s i * realSignVector m s j) by intro s; ring]
    rw [finiteAverage_mul, realSignVector_covariance]
  simp_rw [hcov]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  have hi : A (Pi.single i 1) = T (b i) := by
    simp [A, Module.Basis.equivFun_symm_apply, Pi.single_apply]
  rw [hi, real_inner_self_eq_norm_sq]
  ring

theorem hilbert_norm_basis_sign_le {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (T : E ≃L[ℝ] H)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ x, ‖T x‖ ≤ ‖x‖) (hhi : ∀ x, ‖x‖ ≤ D * ‖T x‖)
    (s : SignIndex m) (a : Fin m → ℝ) :
    ‖T (b.equivFun.symm (fun i => realSignVector m s i * a i))‖ ≤
      ((K : ℝ) * D) * ‖T (b.equivFun.symm a)‖ := by
  rw [← basisMultiplier_equivFun_symm]
  calc
    _ ≤ ‖basisMultiplier b (realSignVector m s) (b.equivFun.symm a)‖ := hlo _
    _ ≤ (K : ℝ) * ‖b.equivFun.symm a‖ := norm_basisMultiplier_le_bound b K hb
      ⟨realSignVector m s, by intro i; rw [Real.norm_eq_abs, abs_realSignVector]⟩ _
    _ ≤ (K : ℝ) * (D * ‖T (b.equivFun.symm a)‖) :=
      mul_le_mul_of_nonneg_left (hhi _) K.2
    _ = _ := by ring

theorem unconditional_hilbert_synthesis_sq_bounds {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (T : E ≃L[ℝ] H)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ x, ‖T x‖ ≤ ‖x‖) (hhi : ∀ x, ‖x‖ ≤ D * ‖T x‖)
    (hnorm : ∀ i, ‖T (b i)‖ = 1) (a : Fin m → ℝ) :
    ‖T (b.equivFun.symm a)‖ ^ 2 ≤ ((K : ℝ) * D) ^ 2 * (∑ i, a i ^ 2) ∧
      (∑ i, a i ^ 2) ≤ ((K : ℝ) * D) ^ 2 * ‖T (b.equivFun.symm a)‖ ^ 2 := by
  have havg : finiteAverage (fun s =>
      ‖T (b.equivFun.symm (fun i => realSignVector m s i * a i))‖ ^ 2) =
      ∑ i, a i ^ 2 := by
    have h := finiteAverage_basis_sign_norm_sq b T.toLinearMap a
    change finiteAverage (fun s =>
      ‖T (b.equivFun.symm (fun i => realSignVector m s i * a i))‖ ^ 2) =
      ∑ i, a i ^ 2 * ‖T (b i)‖ ^ 2 at h
    simpa only [hnorm, one_pow, mul_one] using h
  constructor
  · have hpoint (s : SignIndex m) : ‖T (b.equivFun.symm a)‖ ^ 2 ≤
        ((K : ℝ) * D) ^ 2 *
          ‖T (b.equivFun.symm (fun i => realSignVector m s i * a i))‖ ^ 2 := by
      have hinv : (fun i => realSignVector m s i * (realSignVector m s i * a i)) = a := by
        funext i
        rw [← mul_assoc, ← pow_two, realSignVector_coordinate_sq, one_mul]
      have h := hilbert_norm_basis_sign_le b T K hb hD hlo hhi s
        (fun i => realSignVector m s i * a i)
      rw [hinv] at h
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
    have h := finiteAverage_mono _ _ hpoint
    simpa only [finiteAverage_const, finiteAverage_mul, havg] using h
  · have hpoint (s : SignIndex m) :
        ‖T (b.equivFun.symm (fun i => realSignVector m s i * a i))‖ ^ 2 ≤
          ((K : ℝ) * D) ^ 2 * ‖T (b.equivFun.symm a)‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (hilbert_norm_basis_sign_le b T K hb hD hlo hhi s a) 2
    have h := finiteAverage_mono _ _ hpoint
    simpa only [havg, finiteAverage_const] using h

theorem unconditional_hilbert_synthesis_bounds {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (T : E ≃L[ℝ] H)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ x, ‖T x‖ ≤ ‖x‖) (hhi : ∀ x, ‖x‖ ≤ D * ‖T x‖)
    (hnorm : ∀ i, ‖T (b i)‖ = 1) (a : Fin m → ℝ) :
    ‖T (b.equivFun.symm a)‖ ≤ ((K : ℝ) * D) * ‖WithLp.toLp 2 a‖ ∧
      ‖WithLp.toLp 2 a‖ ≤ ((K : ℝ) * D) * ‖T (b.equivFun.symm a)‖ := by
  have h := unconditional_hilbert_synthesis_sq_bounds b T K hb hD hlo hhi hnorm a
  rw [← EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 a)] at h
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg K.2 hD) (norm_nonneg _))).mp
    rw [mul_pow]
    exact h.1
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg K.2 hD) (norm_nonneg _))).mp
    rw [mul_pow]
    exact h.2

end ComplementedSubspace
