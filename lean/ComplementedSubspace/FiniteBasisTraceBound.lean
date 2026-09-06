import ComplementedSubspace.FiniteProjectionTrace
import ComplementedSubspace.HilbertTraceTransfer
import ComplementedSubspace.LocalUnconditional

/-! # The analytic trace-defect bound for a finite unconditional basis -/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace ComplementedSubspace

variable {E W Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem basisSignMultiplier_eq {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (s : SignIndex m) (w : Fin m → ℝ) :
    basisSignMultiplier b s w =
      (basisMultiplier b (fun i => realSignVector m s i * w i)).toLinearMap := by
  classical
  apply b.ext
  intro i
  simp [basisSignMultiplier, basisCoordinateMap, Module.Basis.coord_apply,
    Finsupp.single_apply]

theorem abs_realSignVector (m : ℕ) (s : SignIndex m) (i : Fin m) :
    |realSignVector m s i| = 1 := by
  have h := realSignVector_coordinate_sq m s i
  have hsq := sq_abs (realSignVector m s i)
  have hnn := abs_nonneg (realSignVector m s i)
  nlinarith

theorem norm_basisSignMultiplier_le {m : ℕ} (b : Module.Basis (Fin m) ℝ Y)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    (s : SignIndex m) (w : Fin m → ℝ) (hw : ∀ i, |w i| ≤ 1) :
    ‖basisMultiplier b (fun i => realSignVector m s i * w i)‖ ≤ (K : ℝ) := by
  have hθ (i : Fin m) : ‖realSignVector m s i * w i‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_realSignVector, one_mul]
    exact hw i
  exact NNReal.coe_le_coe.mpr
    (enorm_le_coe.mp ((enorm_basisMultiplier_le b _ hθ).trans hb))

private theorem norm_sandwich_le {A B C F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : A →L[ℝ] B) (T : B →L[ℝ] C) (R : C →L[ℝ] F)
    (hI : ∀ x, ‖I x‖ ≤ ‖x‖) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    {K : ℝ} (hK : 0 ≤ K) (hT : ‖T‖ ≤ K) : ‖R.comp (T.comp I)‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  calc
    ‖R (T (I x))‖ ≤ ‖T (I x)‖ := hR _
    _ ≤ ‖T‖ * ‖I x‖ := T.le_opNorm _
    _ ≤ K * ‖x‖ := mul_le_mul hT (hI x) (norm_nonneg _) hK

/-- Exact finite trace defect, bounded using only contractive decomposition
maps, the finite basis constant, local Hilbert approximation, and the explicit
Hilbert trace estimate. -/
theorem finite_basis_trace_defect_le {m q : ℕ}
    (b : Module.Basis (Fin m) ℝ Y)
    (I : E →L[ℝ] Y) (R : Y →L[ℝ] E) (J : W →L[ℝ] Y) (S : Y →L[ℝ] W)
    (hJS : J.comp S = ContinuousLinearMap.id ℝ Y - I.comp R)
    (hI : ∀ x, ‖I x‖ ≤ ‖x‖) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (K : ℝ≥0) (hb : unconditionalBasisConstant b ≤ (K : ℝ≥0∞))
    {D a : ℝ} (hD : 0 ≤ D) (ha : 0 ≤ a) (hE : Module.finrank ℝ E ≤ q)
    (hlocal : ∀ (F : Submodule ℝ W) [FiniteDimensional ℝ F], Module.finrank ℝ F ≤ q →
      HasHilbertNormWithin F D)
    (htrace : ∀ (F : Submodule ℝ W) [FiniteDimensional ℝ F]
      (p : HilbertNormModel F) (U : E →L[ℝ] p.Space) (V : p.Space →L[ℝ] E),
      |LinearMap.trace ℝ E (V.comp U).toLinearMap| ≤ a * ‖U‖ * ‖V‖) :
    (∑ i, |LinearMap.trace ℝ E (compressedBasisMap b I.toLinearMap R.toLinearMap i) -
      (LinearMap.trace ℝ E (compressedBasisMap b I.toLinearMap R.toLinearMap i)) ^ 2|) ≤
      a * D * (K : ℝ) ^ 2 := by
  apply sum_abs_compressed_trace_defect_le
  intro w hw s
  let M := basisMultiplier b (fun i => realSignVector m s i * (1 : ℝ))
  let N := basisMultiplier b (fun i => realSignVector m s i * w i)
  let A := S.comp (N.comp I)
  let B := R.comp (M.comp J)
  have hA : ‖A‖ ≤ (K : ℝ) := norm_sandwich_le I N S hI hS K.2
    (norm_basisSignMultiplier_le b K hb s w hw)
  have hB : ‖B‖ ≤ (K : ℝ) := norm_sandwich_le J M R hJ hR K.2
    (norm_basisSignMultiplier_le b K hb s (fun _ => 1) (by intro i; norm_num))
  have heq : (B.comp A).toLinearMap =
      basisComplementCompression b I.toLinearMap R.toLinearMap s w := by
    ext x
    simp only [basisComplementCompression, basisSignMultiplier_eq, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, LinearMap.sub_apply, LinearMap.id_apply]
    change R (M (J (S (N (I x))))) = R (M (N (I x) - I (R (N (I x)))))
    have h := congrArg (fun f : Y →L[ℝ] Y => f (N (I x))) hJS
    exact congrArg (fun y => R (M y)) h
  rw [← heq]
  calc
    |LinearMap.trace ℝ E (B.comp A).toLinearMap| ≤ a * D * ‖A‖ * ‖B‖ :=
      trace_comp_le_of_localHilbert hD ha hE hlocal htrace A B
    _ ≤ a * D * (K : ℝ) * (K : ℝ) := by
      have hprod := mul_le_mul hA hB (norm_nonneg B) K.2
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hprod (mul_nonneg ha hD)
    _ = a * D * (K : ℝ) ^ 2 := by ring

end ComplementedSubspace
