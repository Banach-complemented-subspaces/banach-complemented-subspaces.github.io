import ComplementedSubspace.FiniteSigns
import ComplementedSubspace.FiniteTraceSelection
import Mathlib.LinearAlgebra.Trace

/-!
# Finite coordinate compressions and their trace defects

The algebraic identities here are exact. Analytic bounds on the complementary
factorizations are supplied separately by the local Hilbert estimates.
-/

noncomputable section
open scoped BigOperators

namespace ComplementedSubspace

theorem realSignVector_covariance (m : ℕ) (i j : Fin m) :
    finiteAverage (fun s => realSignVector m s i * realSignVector m s j) =
      if i = j then 1 else 0 := by
  classical
  have h := realSignSum_covariance m (Pi.single i 1) (Pi.single j 1)
  simpa [realSignSum_eq_dot, Pi.single_apply, eq_comm] using h

theorem finiteAverage_sign_bilinear (m : ℕ) (c : Fin m → Fin m → ℝ) :
    finiteAverage (fun s => ∑ i, ∑ j,
      realSignVector m s i * realSignVector m s j * c i j) = ∑ i, c i i := by
  classical
  simp_rw [finiteAverage_sum]
  have h (i j : Fin m) :
      finiteAverage (fun s => realSignVector m s i * realSignVector m s j * c i j) =
        (if i = j then 1 else 0) * c i j := by
    simp_rw [mul_comm _ (c i j)]
    rw [finiteAverage_mul, realSignVector_covariance]
  simp_rw [h]
  simp

variable {E Y : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ E]

def basisCoordinateMap {m : ℕ} (b : Module.Basis (Fin m) ℝ Y) (i : Fin m) :
    Y →ₗ[ℝ] Y := (b.coord i).smulRight (b i)

def compressedBasisMap {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E) (i : Fin m) : E →ₗ[ℝ] E :=
  R.comp ((basisCoordinateMap b i).comp I)

theorem compressedBasisMap_eq_smulRight {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E) (i : Fin m) :
    compressedBasisMap b I R i = ((b.coord i).comp I).smulRight (R (b i)) := by
  ext x
  simp only [compressedBasisMap, basisCoordinateMap, LinearMap.comp_apply,
    LinearMap.smulRight_apply, map_smul]

theorem compressedBasisMap_trace {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E) (i : Fin m) :
    LinearMap.trace ℝ E (compressedBasisMap b I R i) = b.coord i (I (R (b i))) := by
  rw [compressedBasisMap_eq_smulRight, LinearMap.trace_smulRight]
  rfl

theorem compressedBasisMap_trace_square {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E) (i : Fin m) :
    LinearMap.trace ℝ E ((compressedBasisMap b I R i).comp
      (compressedBasisMap b I R i)) =
      (LinearMap.trace ℝ E (compressedBasisMap b I R i)) ^ 2 := by
  rw [compressedBasisMap_trace]
  have hmap : (compressedBasisMap b I R i).comp (compressedBasisMap b I R i) =
      (b.coord i (I (R (b i)))) • compressedBasisMap b I R i := by
    ext x
    simp only [compressedBasisMap_eq_smulRight, LinearMap.comp_apply,
      LinearMap.smulRight_apply, LinearMap.smul_apply, map_smul, smul_smul]
    congr 1
    ring
  rw [hmap, map_smul, compressedBasisMap_trace, smul_eq_mul, pow_two]

theorem sum_basisCoordinateMap {m : ℕ} (b : Module.Basis (Fin m) ℝ Y) :
    (∑ i, basisCoordinateMap b i) = LinearMap.id := by
  ext y
  simpa only [LinearMap.sum_apply, basisCoordinateMap, LinearMap.smulRight_apply,
    Module.Basis.coord_apply, LinearMap.id_apply] using b.sum_repr y

theorem sum_compressedBasisMap {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E) (hRI : R.comp I = LinearMap.id) :
    (∑ i, compressedBasisMap b I R i) = LinearMap.id := by
  ext x
  calc
    (∑ i, compressedBasisMap b I R i) x = R ((∑ i, basisCoordinateMap b i) (I x)) := by
      simp only [compressedBasisMap, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    _ = x := by
      rw [sum_basisCoordinateMap, LinearMap.id_apply]
      exact congrArg (fun f : E →ₗ[ℝ] E => f x) hRI

theorem sum_compressedBasisMap_trace {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E) (hRI : R.comp I = LinearMap.id) :
    (∑ i, LinearMap.trace ℝ E (compressedBasisMap b I R i)) =
      (Module.finrank ℝ E : ℝ) := by
  rw [← map_sum, sum_compressedBasisMap b I R hRI, LinearMap.trace_id]

theorem compressedBasisMap_complement_defect {m : ℕ}
    (b : Module.Basis (Fin m) ℝ Y) (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E) (i : Fin m) :
    R.comp ((basisCoordinateMap b i).comp
      ((LinearMap.id - I.comp R).comp ((basisCoordinateMap b i).comp I))) =
      compressedBasisMap b I R i -
        (compressedBasisMap b I R i).comp (compressedBasisMap b I R i) := by
  ext x
  simp only [compressedBasisMap, basisCoordinateMap, LinearMap.comp_apply,
    LinearMap.smulRight_apply, LinearMap.sub_apply, LinearMap.id_apply,
    map_sub, map_smul, smul_sub]
  simp [Module.Basis.coord_apply]

def basisSignMultiplier {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (s : SignIndex m) (w : Fin m → ℝ) : Y →ₗ[ℝ] Y :=
  ∑ i, (realSignVector m s i * w i) • basisCoordinateMap b i

def basisComplementCompression {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E) (s : SignIndex m) (w : Fin m → ℝ) :
    E →ₗ[ℝ] E :=
  R.comp ((basisSignMultiplier b s (fun _ => 1)).comp
    ((LinearMap.id - I.comp R).comp ((basisSignMultiplier b s w).comp I)))

theorem basisComplementCompression_expansion {m : ℕ}
    (b : Module.Basis (Fin m) ℝ Y) (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E)
    (s : SignIndex m) (w : Fin m → ℝ) :
    basisComplementCompression b I R s w = ∑ i, ∑ j,
      (realSignVector m s i * realSignVector m s j * w j) •
        (R.comp ((basisCoordinateMap b i).comp
          ((LinearMap.id - I.comp R).comp ((basisCoordinateMap b j).comp I)))) := by
  ext x
  simp only [basisComplementCompression, basisSignMultiplier,
    LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Finset.smul_sum, smul_smul, mul_one, mul_assoc]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm, mul_assoc]

/-- Averaging the complementary composition gives precisely the weighted
trace defect. No estimate on that composition is assumed in this identity. -/
theorem finiteAverage_basisComplementCompression_trace {m : ℕ}
    (b : Module.Basis (Fin m) ℝ Y) (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E)
    (w : Fin m → ℝ) :
    finiteAverage (fun s => LinearMap.trace ℝ E (basisComplementCompression b I R s w)) =
      ∑ i, w i * (LinearMap.trace ℝ E (compressedBasisMap b I R i) -
        (LinearMap.trace ℝ E (compressedBasisMap b I R i)) ^ 2) := by
  let c : Fin m → Fin m → ℝ := fun i j => w j * LinearMap.trace ℝ E
    (R.comp ((basisCoordinateMap b i).comp
      ((LinearMap.id - I.comp R).comp ((basisCoordinateMap b j).comp I))))
  have hpoint (s : SignIndex m) :
      LinearMap.trace ℝ E (basisComplementCompression b I R s w) =
        ∑ i, ∑ j, realSignVector m s i * realSignVector m s j * c i j := by
    rw [basisComplementCompression_expansion]
    simp only [map_sum, map_smul, smul_eq_mul, c, mul_assoc]
  simp_rw [hpoint]
  rw [finiteAverage_sign_bilinear]
  apply Finset.sum_congr rfl
  intro i _
  simp only [c, compressedBasisMap_complement_defect, map_sub,
    compressedBasisMap_trace_square]

/-- A uniform analytic bound on the complementary compositions controls the
total scalar trace defect. Its analytic hypothesis must be proved in each
application; it is not part of the definition of the coefficient spaces. -/
theorem sum_abs_compressed_trace_defect_le {m : ℕ}
    (b : Module.Basis (Fin m) ℝ Y) (I : E →ₗ[ℝ] Y) (R : Y →ₗ[ℝ] E)
    {M : ℝ}
    (hbound : ∀ (w : Fin m → ℝ), (∀ i, |w i| ≤ 1) →
      ∀ s : SignIndex m,
        |LinearMap.trace ℝ E (basisComplementCompression b I R s w)| ≤ M) :
    (∑ i, |LinearMap.trace ℝ E (compressedBasisMap b I R i) -
      (LinearMap.trace ℝ E (compressedBasisMap b I R i)) ^ 2|) ≤ M := by
  classical
  let d : Fin m → ℝ := fun i => LinearMap.trace ℝ E (compressedBasisMap b I R i) -
    (LinearMap.trace ℝ E (compressedBasisMap b I R i)) ^ 2
  let w : Fin m → ℝ := fun i => if 0 ≤ d i then 1 else -1
  have hw (i : Fin m) : |w i| ≤ 1 := by
    dsimp [w]
    split_ifs <;> norm_num
  have hwd (i : Fin m) : w i * d i = |d i| := by
    dsimp [w]
    split_ifs with hi
    · rw [one_mul, abs_of_nonneg hi]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge hi)]
  have htrace := finiteAverage_basisComplementCompression_trace b I R w
  change finiteAverage (fun s => LinearMap.trace ℝ E
    (basisComplementCompression b I R s w)) = ∑ i, w i * d i at htrace
  simp_rw [hwd] at htrace
  change (∑ i, |d i|) ≤ M
  rw [← htrace]
  calc
    finiteAverage (fun s => LinearMap.trace ℝ E (basisComplementCompression b I R s w)) ≤
        finiteAverage (fun _ : SignIndex m => M) :=
      finiteAverage_mono _ _ (fun s => (le_abs_self _).trans (hbound w hw s))
    _ = M := finiteAverage_const M

end ComplementedSubspace
