import ComplementedSubspace.FiniteCorrection
import ComplementedSubspace.BasisTransport

/-!
# From approximate finite containment to exact superspaces

The constants below refer to the inherited ambient norm. A common finite
unconditional span approximating the basis of V can be pulled back by an
automorphism to an actual finite unconditional superspace of V.
-/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Simultaneous finite approximation with a uniformly controlled finite
unconditional basis. This property alone does not assume exact containment. -/
def HasFiniteUnconditionalApproximations (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : ℝ≥0) : Prop :=
  ∀ (m : ℕ) (x : Fin m → E) (δ : ℝ), 0 < δ →
    ∃ (F : Submodule ℝ E) (n : ℕ) (b : Module.Basis (Fin n) ℝ F),
      unconditionalBasisConstant b ≤ (C : ℝ≥0∞) ∧
      ∀ i, ∃ y : F, ‖(y : E) - x i‖ ≤ δ

/-- Fixing V and a permissible perturbation size gives one tolerance valid
for every approximating finite span. -/
theorem exists_tolerance_for_finite_superspace (V : Submodule ℝ E)
    [FiniteDimensional ℝ V] {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (m : ℕ) (v : Fin m → E) (δ : ℝ), 0 < δ ∧
      ∀ (F : Submodule ℝ E),
        (∀ i, ∃ y : F, ‖(y : E) - v i‖ ≤ δ) →
        ∃ (T : E ≃L[ℝ] E), V ≤ F.comap T.toLinearMap ∧
          ‖T.toContinuousLinearMap‖ ≤ 1 + ε ∧
          ‖T.symm.toContinuousLinearMap‖ ≤ (1 - ε)⁻¹ := by
  classical
  let m := Module.finrank ℝ V
  let b := Module.finBasis ℝ V
  obtain ⟨φ, hφ, _⟩ := exists_extended_basis_coordinates V b
  let M : ℝ := ∑ i, ‖φ i‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let δ : ℝ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε0 (by linarith)
  refine ⟨m, fun i => (b i : E), δ, hδ, ?_⟩
  intro F happ
  choose w hw using happ
  have hcoord : ∀ i j, φ i (b j : E) = if i = j then 1 else 0 := by
    intro i j
    rw [hφ]
    simp [Module.Basis.equivFun_apply, eq_comm]
  have herr : (∑ i, ‖φ i‖ * ‖(w i : E) - (b i : E)‖) ≤ ε := by
    calc
      _ ≤ ∑ i, ‖φ i‖ * δ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hw i) (norm_nonneg _)
      _ = M * δ := by rw [← Finset.sum_mul]
      _ ≤ (M + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε := by dsimp [δ]; field_simp
  obtain ⟨T, hT, hnorm, hinv⟩ := exists_equiv_of_weighted_errors φ
    (fun i => (b i : E)) (fun i => (w i : E)) hcoord hε1 herr
  refine ⟨T, ?_, hnorm, hinv⟩
  intro x hx
  change T x ∈ F
  let xv : V := ⟨x, hx⟩
  have hrepr : x = ∑ i, b.repr xv i • (b i : E) := by
    have h := congrArg (fun y : V => (y : E)) (b.sum_repr xv)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h.symm
  rw [hrepr, map_sum]
  apply F.sum_mem
  intro i _
  rw [map_smul, hT]
  exact F.smul_mem _ (w i).property

def correctionInverseBound {ε : ℝ} (hε : ε < 1) : ℝ≥0 :=
  ⟨(1 - ε)⁻¹, inv_nonneg.mpr (sub_pos.mpr hε).le⟩

def correctionForwardBound {ε : ℝ} (hε : 0 < ε) : ℝ≥0 :=
  ⟨1 + ε, by linarith⟩

/-- Quantitative exact containment obtained from simultaneous approximation.
The factor tends to one with the perturbation size. -/
theorem lambdaDPR_le_of_finite_approximations
    (C : ℝ≥0) (happ : HasFiniteUnconditionalApproximations E C)
    (V : Submodule ℝ E) [FiniteDimensional ℝ V]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    lambdaDPR E V ≤ max 1
      ((correctionInverseBound hε1 * C * correctionForwardBound hε0 : ℝ≥0) : ℝ≥0∞) := by
  classical
  obtain ⟨m, v, δ, hδ, htol⟩ := exists_tolerance_for_finite_superspace V hε0 hε1
  obtain ⟨F, n, b, hb, happrox⟩ := happ m v δ hδ
  obtain ⟨T, hVT, hnorm, hinv⟩ := htol F happrox
  let G := F.comap T.toLinearMap
  let e : F ≃L[ℝ] G := (T.ofSubmodule' F).symm
  let A : ℝ≥0 := ⟨(1 - ε)⁻¹, inv_nonneg.mpr (sub_pos.mpr hε1).le⟩
  let B : ℝ≥0 := ⟨1 + ε, by linarith⟩
  have he (x : F) : ‖e x‖ ≤ (A : ℝ) * ‖x‖ :=
    (T.symm.toContinuousLinearMap.le_opNorm (x : E)).trans
      (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  have hi (y : G) : ‖e.symm y‖ ≤ (B : ℝ) * ‖y‖ :=
    (T.toContinuousLinearMap.le_opNorm (y : E)).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  let bG := b.map e.toLinearEquiv
  letI : FiniteDimensional ℝ G := Module.Finite.of_basis bG
  calc
    lambdaDPR E V ≤ unconditionalConstant G := lambdaDPR_le_of_le E hVT inferInstance
    _ ≤ unconditionalBasisConstant bG :=
      iInf_le_of_le n (iInf_le_of_le bG le_rfl)
    _ ≤ max 1 ((A * C * B : ℝ≥0) : ℝ≥0∞) :=
      unconditionalBasisConstant_map_le b e A B C hb he hi

theorem chiDPR_le_of_finite_approximations
    (C : ℝ≥0) (happ : HasFiniteUnconditionalApproximations E C)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    chiDPR E ≤ max 1
      ((correctionInverseBound hε1 * C * correctionForwardBound hε0 : ℝ≥0) : ℝ≥0∞) := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun _ => ?_
  letI : FiniteDimensional ℝ V := hV
  exact lambdaDPR_le_of_finite_approximations C happ V hε0 hε1

/-- For qualitative corollaries, any fixed small perturbation suffices. -/
theorem hasDPR_of_finite_approximations
    (C : ℝ≥0) (happ : HasFiniteUnconditionalApproximations E C) :
    HasDPRLocalUnconditionalStructure E := by
  apply (chiDPR_le_of_finite_approximations C happ
    (ε := 1 / 2) (by norm_num) (by norm_num)).trans_lt
  exact max_lt (by simp) ENNReal.coe_lt_top

/-- Arbitrarily small corrections preserve the optimal numerical bound.
No infimum needs to be attained. -/
theorem chiDPR_le_constant_of_finite_approximations
    (C : ℝ≥0) (hC : 1 ≤ C) (happ : HasFiniteUnconditionalApproximations E C) :
    chiDPR E ≤ (C : ℝ≥0∞) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  have hc : (1 : ℝ) ≤ C := NNReal.coe_le_coe.mpr hC
  have hd : (0 : ℝ) < δ := NNReal.coe_pos.mpr hδ
  let ε : ℝ := (δ : ℝ) / (2 * (C : ℝ) + δ)
  have hden : 0 < 2 * (C : ℝ) + δ := by linarith
  have he0 : 0 < ε := div_pos hd hden
  have he1 : ε < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have heq : ε * (2 * (C : ℝ) + δ) = δ := div_mul_cancel₀ _ hden.ne'
  apply (chiDPR_le_of_finite_approximations C happ he0 he1).trans
  apply max_le
  · exact (ENNReal.coe_le_coe.mpr hC).trans (le_add_right le_rfl)
  · rw [← ENNReal.coe_add]
    apply ENNReal.coe_le_coe.mpr
    apply NNReal.coe_le_coe.mp
    change (1 - ε)⁻¹ * (C : ℝ) * (1 + ε) ≤ (C : ℝ) + δ
    calc
      (1 - ε)⁻¹ * (C : ℝ) * (1 + ε) = ((C : ℝ) * (1 + ε)) / (1 - ε) := by ring
      _ ≤ (C : ℝ) + δ := (div_le_iff₀ (sub_pos.mpr he1)).mpr (by nlinarith [heq])

theorem chiGL_le_constant_of_finite_approximations
    (C : ℝ≥0) (hC : 1 ≤ C) (happ : HasFiniteUnconditionalApproximations E C) :
    chiGL E ≤ (C : ℝ≥0∞) :=
  (chiGL_le_chiDPR E).trans (chiDPR_le_constant_of_finite_approximations C hC happ)

end ComplementedSubspace
