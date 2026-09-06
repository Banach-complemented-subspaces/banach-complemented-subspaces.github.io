import ComplementedSubspace.AmbientProjection
import ComplementedSubspace.ReindexedFrameProjection

/-! Alternating block projections on the ambient space selected by the finite recursion. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

theorem complement_idempotent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (hP : P.comp P = P) :
    (ContinuousLinearMap.id ℝ E - P).comp (ContinuousLinearMap.id ℝ E - P) =
      ContinuousLinearMap.id ℝ E - P := by
  ext x
  have h := congrArg (fun T : E →L[ℝ] E => T x) hP
  change (x - P x) - P (x - P x) = x - P x
  rw [map_sub]
  change P (P x) = P x at h
  rw [h, sub_self, sub_zero]

namespace RecursiveFrameSelection
variable {η : ℝ} {θ : ℕ → ℝ} (s : RecursiveFrameSelection η θ)

/-- Even blocks select the frame range; odd blocks select its complement. -/
def alternatingBlockProjection (j : ℕ) :
    Block s.toBlockParameters j →L[ℝ] Block s.toBlockParameters j :=
  if Even j then s.blockFrameProjection j else
    ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) - s.blockFrameProjection j

theorem alternatingBlockProjection_idempotent (j : ℕ) :
    (s.alternatingBlockProjection j).comp (s.alternatingBlockProjection j) =
      s.alternatingBlockProjection j := by
  dsimp [alternatingBlockProjection]
  split_ifs
  · exact s.blockFrameProjection_idempotent j
  · exact complement_idempotent _ (s.blockFrameProjection_idempotent j)

theorem alternatingBlockProjection_norm_le {B : ℝ} (hB : Real.exp (18 * η) ≤ B)
    (hcomplement : ∀ j, ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) -
      s.blockFrameProjection j‖ ≤ B) (j : ℕ) : ‖s.alternatingBlockProjection j‖ ≤ B := by
  dsimp [alternatingBlockProjection]
  split_ifs
  · exact (s.blockFrameProjection_norm_le j).trans hB
  · exact hcomplement j

theorem alternatingBlockProjection_complement_norm_le {B : ℝ}
    (hB : Real.exp (18 * η) ≤ B)
    (hcomplement : ∀ j, ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) -
      s.blockFrameProjection j‖ ≤ B) (j : ℕ) :
    ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) - s.alternatingBlockProjection j‖ ≤ B := by
  dsimp [alternatingBlockProjection]
  split_ifs
  · exact hcomplement j
  · rw [sub_sub_cancel]
    exact (s.blockFrameProjection_norm_le j).trans hB

/-- The actual alternating infinite projection, with its bound carried explicitly. -/
def alternatingProjection {B : ℝ} (hB : Real.exp (18 * η) ≤ B)
    (hcomplement : ∀ j, ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) -
      s.blockFrameProjection j‖ ≤ B) : Ambient s.toBlockParameters →L[ℝ] Ambient s.toBlockParameters :=
  lpDiagonal 2 s.alternatingBlockProjection ((Real.exp_pos _).le.trans hB)
    (s.alternatingBlockProjection_norm_le hB hcomplement)

@[simp] theorem alternatingProjection_apply {B : ℝ} (hB : Real.exp (18 * η) ≤ B)
    (hcomplement : ∀ j, ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) -
      s.blockFrameProjection j‖ ≤ B) (x : Ambient s.toBlockParameters) (j : ℕ) :
    s.alternatingProjection hB hcomplement x j = s.alternatingBlockProjection j (x j) := rfl

theorem alternatingProjection_idempotent {B : ℝ} (hB : Real.exp (18 * η) ≤ B)
    (hcomplement : ∀ j, ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) -
      s.blockFrameProjection j‖ ≤ B) :
    (s.alternatingProjection hB hcomplement).comp (s.alternatingProjection hB hcomplement) =
      s.alternatingProjection hB hcomplement :=
  lpDiagonal_idempotent 2 _ _ _ s.alternatingBlockProjection_idempotent

theorem alternatingProjection_norm_le {B : ℝ} (hB : Real.exp (18 * η) ≤ B)
    (hcomplement : ∀ j, ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) -
      s.blockFrameProjection j‖ ≤ B) : ‖s.alternatingProjection hB hcomplement‖ ≤ B :=
  lpDiagonal_norm_le 2 _ _ _

theorem alternatingProjection_complement_norm_le {B : ℝ} (hB : Real.exp (18 * η) ≤ B)
    (hcomplement : ∀ j, ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) -
      s.blockFrameProjection j‖ ≤ B) :
    ‖ContinuousLinearMap.id ℝ (Ambient s.toBlockParameters) -
      s.alternatingProjection hB hcomplement‖ ≤ B :=
  lpDiagonal_complement_norm_le 2 _ _ _ ((Real.exp_pos _).le.trans hB)
    (s.alternatingBlockProjection_complement_norm_le hB hcomplement)

theorem one_le_alternatingProjection_norm {B : ℝ} (hB : Real.exp (18 * η) ≤ B)
    (hcomplement : ∀ j, ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) -
      s.blockFrameProjection j‖ ≤ B) : 1 ≤ ‖s.alternatingProjection hB hcomplement‖ := by
  have h := lpDiagonal_component_norm_le 2 s.alternatingBlockProjection
    ((Real.exp_pos _).le.trans hB) (s.alternatingBlockProjection_norm_le hB hcomplement) 0
  change ‖s.alternatingBlockProjection 0‖ ≤ ‖s.alternatingProjection hB hcomplement‖ at h
  have heven : Even (0 : ℕ) := by decide
  simpa only [alternatingBlockProjection, if_pos heven] using
    (s.one_le_blockFrameProjection_norm 0).trans h

theorem one_le_alternatingProjection_complement_norm {B : ℝ}
    (hB : Real.exp (18 * η) ≤ B)
    (hcomplement : ∀ j, ‖ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) -
      s.blockFrameProjection j‖ ≤ B) :
    1 ≤ ‖ContinuousLinearMap.id ℝ (Ambient s.toBlockParameters) -
      s.alternatingProjection hB hcomplement‖ := by
  have hB0 := (Real.exp_pos _).le.trans hB
  have h := lpDiagonal_component_norm_le 2
    (fun j => ContinuousLinearMap.id ℝ (Block s.toBlockParameters j) - s.alternatingBlockProjection j)
    hB0 (s.alternatingBlockProjection_complement_norm_le hB hcomplement) 1
  rw [← lpDiagonal_complement_eq 2 s.alternatingBlockProjection hB0
    (s.alternatingBlockProjection_norm_le hB hcomplement) hB0
    (s.alternatingBlockProjection_complement_norm_le hB hcomplement)] at h
  have hodd : ¬ Even (1 : ℕ) := by decide
  simp only [alternatingBlockProjection, if_neg hodd, sub_sub_cancel] at h
  exact (s.one_le_blockFrameProjection_norm 1).trans h

end RecursiveFrameSelection

/-- Uniform projection and complementary projection bounds, with no remaining
finite-block norm premise. The quadratic scale can be chosen arbitrarily small. -/
theorem exists_recursive_alternatingProjection_tolerance {D : ℝ} (hD : 1 < D) :
    ∃ η₀ > 0, ∀ {η : ℝ}, η ≤ η₀ → ∀ {θ : ℕ → ℝ} (s : RecursiveFrameSelection η θ),
      ∃ P : Ambient s.toBlockParameters →L[ℝ] Ambient s.toBlockParameters,
        P.comp P = P ∧ 1 ≤ ‖P‖ ∧ ‖P‖ ≤ D ^ 2 * Real.exp (18 * η) ∧
        1 ≤ ‖ContinuousLinearMap.id ℝ (Ambient s.toBlockParameters) - P‖ ∧
        ‖ContinuousLinearMap.id ℝ (Ambient s.toBlockParameters) - P‖ ≤
          D ^ 2 * Real.exp (18 * η) ∧
        ∀ x j, P x j = s.alternatingBlockProjection j (x j) := by
  obtain ⟨η₀, hη₀, hbound⟩ := exists_recursive_complement_tolerance hD
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη θ s
  have hDsq : 1 ≤ D ^ 2 := by nlinarith only [hD]
  have hB : Real.exp (18 * η) ≤ D ^ 2 * Real.exp (18 * η) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hDsq (Real.exp_pos _).le
  let hc := hbound hη s
  refine ⟨s.alternatingProjection hB hc, s.alternatingProjection_idempotent hB hc,
    s.one_le_alternatingProjection_norm hB hc, s.alternatingProjection_norm_le hB hc,
    s.one_le_alternatingProjection_complement_norm hB hc,
    s.alternatingProjection_complement_norm_le hB hc, ?_⟩
  intro x j
  rfl

/-- The projection part of the construction: both complementary norms are
arbitrarily close to one on the actual recursively selected ambient space. -/
theorem exists_recursive_alternatingProjection_near_one {B : ℝ} (hB : 1 < B) :
    ∃ (η : ℝ) (hη : 0 < η),
      ∃ P : Ambient (recursiveFrameSelection hη).toBlockParameters →L[ℝ]
          Ambient (recursiveFrameSelection hη).toBlockParameters,
        P.comp P = P ∧ 1 ≤ ‖P‖ ∧ ‖P‖ < B ∧
        1 ≤ ‖ContinuousLinearMap.id ℝ (Ambient (recursiveFrameSelection hη).toBlockParameters) - P‖ ∧
        ‖ContinuousLinearMap.id ℝ (Ambient (recursiveFrameSelection hη).toBlockParameters) - P‖ < B ∧
        ∀ x j, P x j = (recursiveFrameSelection hη).alternatingBlockProjection j (x j) := by
  let D : ℝ := Real.sqrt ((B + 1) / 2)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = (B + 1) / 2 := Real.sq_sqrt (by linarith)
  have hD : 1 < D := by nlinarith only [hDsq, hD0, hB]
  have hDsqB : D ^ 2 < B := by linarith only [hDsq, hB]
  obtain ⟨η₀, hη₀, hconstruct⟩ := exists_recursive_alternatingProjection_tolerance hD
  have hc : ContinuousAt (fun t : ℝ => D ^ 2 * Real.exp (18 * t)) 0 := by fun_prop
  have ht : Filter.Tendsto (fun t : ℝ => D ^ 2 * Real.exp (18 * t)) (nhds 0) (nhds (D ^ 2)) := by
    simpa using hc.tendsto
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (ht.eventually (gt_mem_nhds hDsqB))
  let η : ℝ := min η₀ δ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηle : η ≤ η₀ := by
    have h := min_le_left η₀ δ
    dsimp [η]
    linarith
  have hηδ : dist η 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hη]
    have h := min_le_right η₀ δ
    dsimp [η]
    linarith
  have hfinal : D ^ 2 * Real.exp (18 * η) < B := hball hηδ
  obtain ⟨P, hPP, hP1, hP, hPc1, hPc, happly⟩ := hconstruct hηle (recursiveFrameSelection hη)
  exact ⟨η, hη, P, hPP, hP1, hP.trans_lt hfinal, hPc1, hPc.trans_lt hfinal, happly⟩

end ComplementedSubspace
