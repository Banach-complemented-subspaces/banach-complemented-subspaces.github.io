import ComplementedSubspace.Ambient
import Mathlib.Analysis.Normed.Lp.lpHolder

/-! Genuine diagonal operators and projections on dependent `lp` sums. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A uniformly bounded family acts coordinatewise on the actual dependent sum. -/
def lpDiagonal (P : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ i, ‖P i‖ ≤ C) : lp E p →L[𝕜] lp F p := lp.mapCLM p P hC hP

@[simp] theorem lpDiagonal_apply (P : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ i, ‖P i‖ ≤ C) (x : lp E p) (i : ι) :
    lpDiagonal p P hC hP x i = P i (x i) := rfl

theorem lpDiagonal_norm_le (P : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ i, ‖P i‖ ≤ C) : ‖lpDiagonal p P hC hP‖ ≤ C :=
  lp.norm_mapCLM_le p P hC hP

@[simp] theorem lpDiagonal_single [DecidableEq ι] (P : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ i, ‖P i‖ ≤ C) (i : ι) (x : E i) :
    lpDiagonal p P hC hP (lp.single p i x) = lp.single p i (P i x) := by
  classical
  ext j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

theorem lpDiagonal_component_norm_le (P : ∀ i, E i →L[𝕜] F i) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ i, ‖P i‖ ≤ C) (i : ι) : ‖P i‖ ≤ ‖lpDiagonal p P hC hP‖ := by
  classical
  have hp : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) Fact.out
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖P i x‖ = ‖lpDiagonal p P hC hP (lp.single p i x) i‖ := by simp
    _ ≤ ‖lpDiagonal p P hC hP (lp.single p i x)‖ := lp.norm_apply_le_norm hp.ne' _ i
    _ ≤ ‖lpDiagonal p P hC hP‖ * ‖lp.single p i x‖ := (lpDiagonal p P hC hP).le_opNorm _
    _ = ‖lpDiagonal p P hC hP‖ * ‖x‖ := by rw [lp.norm_single hp]

/-- A coordinate formula recovers the uniform block bound from the actual
infinite operator, without retaining its original construction witnesses. -/
theorem block_norm_le_of_coordinate_formula (T : lp E p →L[𝕜] lp F p)
    (P : ∀ i, E i →L[𝕜] F i) (hcoords : ∀ x i, T x i = P i (x i)) (i : ι) :
    ‖P i‖ ≤ ‖T‖ := by
  classical
  have hp : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) Fact.out
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖P i x‖ = ‖T (lp.single p i x) i‖ := by rw [hcoords]; simp
    _ ≤ ‖T (lp.single p i x)‖ := lp.norm_apply_le_norm hp.ne' _ i
    _ ≤ ‖T‖ * ‖lp.single p i x‖ := T.le_opNorm _
    _ = ‖T‖ * ‖x‖ := by rw [lp.norm_single hp]

theorem eq_lpDiagonal_of_coordinate_formula (T : lp E p →L[𝕜] lp F p)
    (P : ∀ i, E i →L[𝕜] F i) (hcoords : ∀ x i, T x i = P i (x i)) :
    T = lpDiagonal p P (norm_nonneg T) (block_norm_le_of_coordinate_formula p T P hcoords) := by
  ext x i
  exact hcoords x i

theorem complement_coordinate_formula (T : lp E p →L[𝕜] lp E p)
    (P : ∀ i, E i →L[𝕜] E i) (hcoords : ∀ x i, T x i = P i (x i)) :
    ∀ x i, (ContinuousLinearMap.id 𝕜 (lp E p) - T) x i =
      (ContinuousLinearMap.id 𝕜 (E i) - P i) (x i) := by
  intro x i
  change x i - T x i = x i - P i (x i)
  rw [hcoords]

theorem lpDiagonal_idempotent (P : ∀ i, E i →L[𝕜] E i) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ i, ‖P i‖ ≤ C) (hIdem : ∀ i, (P i).comp (P i) = P i) :
    (lpDiagonal p P hC hP).comp (lpDiagonal p P hC hP) = lpDiagonal p P hC hP := by
  ext x i
  exact congrArg (fun T : E i →L[𝕜] E i => T (x i)) (hIdem i)

@[simp] theorem lpDiagonal_complement_apply (P : ∀ i, E i →L[𝕜] E i) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ i, ‖P i‖ ≤ C) (x : lp E p) (i : ι) :
    (ContinuousLinearMap.id 𝕜 (lp E p) - lpDiagonal p P hC hP) x i =
      (ContinuousLinearMap.id 𝕜 (E i) - P i) (x i) := rfl

theorem lpDiagonal_complement_eq (P : ∀ i, E i →L[𝕜] E i) {C D : ℝ}
    (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C) (hD : 0 ≤ D)
    (hPc : ∀ i, ‖ContinuousLinearMap.id 𝕜 (E i) - P i‖ ≤ D) :
    ContinuousLinearMap.id 𝕜 (lp E p) - lpDiagonal p P hC hP =
      lpDiagonal p (fun i => ContinuousLinearMap.id 𝕜 (E i) - P i) hD hPc := by
  ext x i
  rfl

theorem lpDiagonal_complement_norm_le (P : ∀ i, E i →L[𝕜] E i) {C D : ℝ}
    (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C) (hD : 0 ≤ D)
    (hPc : ∀ i, ‖ContinuousLinearMap.id 𝕜 (E i) - P i‖ ≤ D) :
    ‖ContinuousLinearMap.id 𝕜 (lp E p) - lpDiagonal p P hC hP‖ ≤ D := by
  rw [lpDiagonal_complement_eq p P hC hP hD hPc]
  exact lpDiagonal_norm_le p _ hD hPc

/-- Specialization to the ambient space in the main theorem. -/
def ambientDiagonalProjection (a : BlockParameters) (P : ∀ j, Block a j →L[ℝ] Block a j)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ j, ‖P j‖ ≤ C) : Ambient a →L[ℝ] Ambient a :=
  lpDiagonal 2 P hC hP

end ComplementedSubspace
