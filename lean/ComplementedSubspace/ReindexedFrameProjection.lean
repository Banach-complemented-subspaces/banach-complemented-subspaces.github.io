import ComplementedSubspace.TensorProjection
import ComplementedSubspace.FiniteLpGeometry
import ComplementedSubspace.LocalHilbertProjection
import ComplementedSubspace.RecursiveParameters

/-! Tensor frame projections on the finite coordinate sets used by the ambient blocks. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

section Transport
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]

def isometricConjugate (e : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) : F →L[ℝ] F :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (P.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem isometricConjugate_apply (e : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) (x : F) :
    isometricConjugate e P x = e (P (e.symm x)) := rfl

theorem isometricConjugate_norm (e : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) :
    ‖isometricConjugate e P‖ = ‖P‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa using P.le_opNorm (e.symm x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa using (isometricConjugate e P).le_opNorm (e x)

theorem isometricConjugate_idempotent (e : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E)
    (hP : P.comp P = P) :
    (isometricConjugate e P).comp (isometricConjugate e P) = isometricConjugate e P := by
  ext x
  simpa only [ContinuousLinearMap.comp_apply, isometricConjugate_apply,
    e.symm_apply_apply] using congrArg (fun T : E →L[ℝ] E => e (T (e.symm x))) hP

theorem isometricConjugate_ne_zero (e : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) (hP : P ≠ 0) :
    isometricConjugate e P ≠ 0 := by
  intro h
  have hnorm := isometricConjugate_norm e P
  rw [h, norm_zero] at hnorm
  exact hP (norm_eq_zero.mp hnorm.symm)

theorem isometricConjugate_complement (e : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) :
    ContinuousLinearMap.id ℝ F - isometricConjugate e P =
      isometricConjugate e (ContinuousLinearMap.id ℝ E - P) := by
  ext x
  simp

end Transport

def frameIndexEquivFin (n : ℕ) : FrameIndex n ≃ Fin (4 ^ n) :=
  Fintype.equivFinOfCardEq (frameIndex_card n)

def framePiLpEquivFin (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    PiLp p (fun _ : FrameIndex n => ℝ) ≃ₗᵢ[ℝ] PiLp p (fun _ : Fin (4 ^ n) => ℝ) :=
  LinearIsometryEquiv.piLpCongrLeft p ℝ ℝ (frameIndexEquivFin n)

def finTensorProjection (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    PiLp p (fun _ : Fin (4 ^ n) => ℝ) →L[ℝ] PiLp p (fun _ : Fin (4 ^ n) => ℝ) :=
  isometricConjugate (framePiLpEquivFin p n) (matrixPiLpCLM p (tensorFrameProjection n))

theorem finTensorProjection_idempotent (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    (finTensorProjection p n).comp (finTensorProjection p n) = finTensorProjection p n :=
  isometricConjugate_idempotent _ _ (tensorFrameProjection_clm_idempotent p n)

theorem finTensorProjection_ne_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    finTensorProjection p n ≠ 0 :=
  isometricConjugate_ne_zero _ _ (matrixPiLpCLM_ne_zero p _ (tensorFrameProjection_ne_zero n))

theorem finTensorProjection_norm_le_exp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (hp3 : p ≤ 3) (n : ℕ) :
    ‖finTensorProjection (ENNReal.ofReal p) n‖ ≤ Real.exp (18 * (n : ℝ) * (p - 2) ^ 2) := by
  rw [finTensorProjection, isometricConjugate_norm]
  exact tensorFrameProjection_norm_le_exp hp hp3 n

theorem exists_finTensorProjection_complement_threshold {D : ℝ} (hD : 1 < D) :
    ∃ ν > 1, ∀ (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)], 2 ≤ p → p ≤ 3 →
      (2 : ℝ) ^ (2 - 4 / p) ≤ ν → ∀ n : ℕ,
      ‖ContinuousLinearMap.id ℝ (PiLp (ENNReal.ofReal p) (fun _ : Fin (4 ^ n) => ℝ)) -
          finTensorProjection (ENNReal.ofReal p) n‖ ≤
        D ^ 2 * Real.exp (18 * (n : ℝ) * (p - 2) ^ 2) := by
  obtain ⟨ν, hν, hlocal⟩ := exists_localHilbert_subspace_threshold.{0} 2 hD
  refine ⟨ν, hν, ?_⟩
  intro p _ hp hp3 hpν n
  have hbase : ApproxParallelogram
      (fun x : PiLp (ENNReal.ofReal p) (fun _ : Fin (4 ^ n) => ℝ) => ‖x‖)
      ((2 : ℝ) ^ (2 - 4 / p)) := finitePiLp_parallelogram_le hp
  have hpar : ApproxParallelogram
      (fun x : PiLp (ENNReal.ofReal p) (fun _ : Fin (4 ^ n) => ℝ) => ‖x‖) ν :=
    hbase.mono hpν
  exact (norm_complement_le_of_localHilbert hD.le (hlocal _ hpar)
    (finTensorProjection (ENNReal.ofReal p) n) (finTensorProjection_idempotent _ n)
    (finTensorProjection_ne_zero _ n)).trans
      (mul_le_mul_of_nonneg_left (finTensorProjection_norm_le_exp hp hp3 n) (sq_nonneg D))

namespace RecursiveFrameSelection
variable {η : ℝ} {θ : ℕ → ℝ} (s : RecursiveFrameSelection η θ)

instance blockFrameExponentFact (j : ℕ) : Fact (1 ≤ ENNReal.ofReal (s.block j).exponent) := by
  constructor
  have h : (1 : ℝ) ≤ (s.block j).exponent := by linarith [(s.block j).two_lt_exponent]
  simpa using ENNReal.ofReal_le_ofReal h

def blockFrameProjection (j : ℕ) : Block s.toBlockParameters j →L[ℝ] Block s.toBlockParameters j :=
  finTensorProjection (ENNReal.ofReal (s.block j).exponent) (s.block j).order

theorem blockFrameProjection_idempotent (j : ℕ) :
    (s.blockFrameProjection j).comp (s.blockFrameProjection j) = s.blockFrameProjection j :=
  finTensorProjection_idempotent _ _

theorem blockFrameProjection_ne_zero (j : ℕ) : s.blockFrameProjection j ≠ 0 :=
  finTensorProjection_ne_zero _ _

theorem one_le_blockFrameProjection_norm (j : ℕ) : 1 ≤ ‖s.blockFrameProjection j‖ := by
  change 1 ≤ ‖isometricConjugate _ _‖
  rw [isometricConjugate_norm]
  exact one_le_tensorFrameProjection_norm _ _

theorem blockFrameProjection_norm_le (j : ℕ) :
    ‖s.blockFrameProjection j‖ ≤ Real.exp (18 * η) := by
  apply (finTensorProjection_norm_le_exp (s.block j).two_lt_exponent.le
    (s.block j).exponent_le_three (s.block j).order).trans
  apply Real.exp_le_exp.mpr
  have h := s.quadratic_error j
  dsimp [FiniteFrameChoice.epsilon] at h
  nlinarith only [h]

end RecursiveFrameSelection

/-- Making the quadratic scale sufficiently small controls every complementary block,
uniformly over every recursive selection. -/
theorem exists_recursive_complement_tolerance {D : ℝ} (hD : 1 < D) :
    ∃ η₀ > 0, ∀ {η : ℝ}, η ≤ η₀ → ∀ {θ : ℕ → ℝ} (s : RecursiveFrameSelection η θ),
      ∀ j, ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) - s.blockFrameProjection j‖ ≤
        D ^ 2 * Real.exp (18 * η) := by
  obtain ⟨ν, hν, hbound⟩ := exists_finTensorProjection_complement_threshold hD
  obtain ⟨δ, hδ, hpδ⟩ := exists_frameExponent_tolerance hν
  refine ⟨δ ^ 2, by positivity, ?_⟩
  intro η hη θ s j
  have hn : (1 : ℝ) ≤ (s.block j).order := by exact_mod_cast (s.block j).order_pos
  have hεsq := mul_le_mul_of_nonneg_right hn (sq_nonneg (s.block j).epsilon)
  have hεsq' : (s.block j).epsilon ^ 2 < δ ^ 2 := by
    calc
      (s.block j).epsilon ^ 2 ≤ ((s.block j).order : ℝ) * (s.block j).epsilon ^ 2 := by
        simpa only [one_mul] using hεsq
      _ < η := s.quadratic_error j
      _ ≤ δ ^ 2 := hη
  have hεδ : (s.block j).epsilon < δ := by nlinarith only [hεsq', hδ]
  have hpν := (hpδ (s.block j).exponent (s.block j).two_lt_exponent.le hεδ).le
  have hb := hbound (s.block j).exponent (s.block j).two_lt_exponent.le
    (s.block j).exponent_le_three hpν (s.block j).order
  change ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) - s.blockFrameProjection j‖ ≤ _ at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg D)
  apply Real.exp_le_exp.mpr
  have h := s.quadratic_error j
  dsimp [FiniteFrameChoice.epsilon] at h
  nlinarith only [h]

end ComplementedSubspace
