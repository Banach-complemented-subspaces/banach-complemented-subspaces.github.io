import ComplementedSubspace.BasisTransport

/-!
# DPR finiteness is invariant under bounded linear isomorphisms

Finite superspaces and their bases are transported within the new ambient
space. This does not assert inheritance under arbitrary retractions.
-/

noncomputable section
open scoped ENNReal NNReal

namespace ComplementedSubspace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem chiDPR_le_transport_of_lt (e : E ≃L[ℝ] F) (C : ℝ≥0)
    (hE : chiDPR E < (C : ℝ≥0∞)) :
    chiDPR F ≤ max 1 ((‖e.toContinuousLinearMap‖₊ * C *
      ‖e.symm.toContinuousLinearMap‖₊ : ℝ≥0) : ℝ≥0∞) := by
  classical
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hV0 => ?_
  letI : FiniteDimensional ℝ V := hV
  let W : Submodule ℝ E := V.comap e.toLinearMap
  let eV : W ≃L[ℝ] V := e.ofSubmodule' V
  letI : FiniteDimensional ℝ W :=
    FiniteDimensional.of_injective eV.toLinearMap eV.injective
  have hW0 : W ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := V.ne_bot_iff.mp hV0
    apply W.ne_bot_iff.mpr
    refine ⟨e.symm v, ?_, ?_⟩
    · change e (e.symm v) ∈ V
      simpa only [e.apply_symm_apply] using hv
    · intro hz
      apply hv0
      have hez := congrArg e hz
      simpa only [e.apply_symm_apply, map_zero] using hez
  have hLocalLE : lambdaDPR E W ≤ chiDPR E := by
    exact le_iSup_of_le W (le_iSup_of_le (inferInstance : FiniteDimensional ℝ W)
      (le_iSup_of_le hW0 le_rfl))
  have hLocal : lambdaDPR E W < (C : ℝ≥0∞) := hLocalLE.trans_lt hE
  simp only [lambdaDPR, unconditionalConstant, iInf_lt_iff] at hLocal
  obtain ⟨G, hWG, hG, n, b, hb⟩ := hLocal
  let H : Submodule ℝ F := G.map e.toLinearMap
  let q : G ≃L[ℝ] H := e.submoduleMap G
  let bH := b.map q.toLinearEquiv
  letI : FiniteDimensional ℝ H := Module.Finite.of_basis bH
  have hVH : V ≤ H := by
    intro v hv
    refine Submodule.mem_map.mpr ⟨e.symm v, hWG ?_, e.apply_symm_apply v⟩
    change e (e.symm v) ∈ V
    simpa only [e.apply_symm_apply] using hv
  have he (x : G) : ‖q x‖ ≤ ‖e.toContinuousLinearMap‖₊ * ‖x‖ :=
    e.toContinuousLinearMap.le_opNorm (x : E)
  have hi (y : H) : ‖q.symm y‖ ≤ ‖e.symm.toContinuousLinearMap‖₊ * ‖y‖ :=
    e.symm.toContinuousLinearMap.le_opNorm (y : F)
  calc
    lambdaDPR F V ≤ unconditionalConstant H :=
      lambdaDPR_le_of_le F hVH inferInstance
    _ ≤ unconditionalBasisConstant bH :=
      iInf_le_of_le n (iInf_le_of_le bH le_rfl)
    _ ≤ _ := unconditionalBasisConstant_map_le b q _ _ C hb.le he hi

theorem HasDPRLocalUnconditionalStructure.of_continuousLinearEquiv
    (hE : HasDPRLocalUnconditionalStructure E) (e : E ≃L[ℝ] F) :
    HasDPRLocalUnconditionalStructure F := by
  obtain ⟨r, hEr, hr⟩ := exists_between hE
  let C := r.toNNReal
  have hC : (C : ℝ≥0∞) = r := ENNReal.coe_toNNReal hr.ne
  have hEC : chiDPR E < (C : ℝ≥0∞) := by rw [hC]; exact hEr
  apply (chiDPR_le_transport_of_lt e C hEC).trans_lt
  exact max_lt (by simp) ENNReal.coe_lt_top

theorem hasDPR_iff_of_continuousLinearEquiv (e : E ≃L[ℝ] F) :
    HasDPRLocalUnconditionalStructure E ↔ HasDPRLocalUnconditionalStructure F :=
  ⟨fun h => h.of_continuousLinearEquiv e,
    fun h => h.of_continuousLinearEquiv e.symm⟩

end ComplementedSubspace
