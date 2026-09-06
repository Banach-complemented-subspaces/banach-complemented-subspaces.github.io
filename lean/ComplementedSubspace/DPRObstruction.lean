import ComplementedSubspace.LocalUnconditional

/-! # From finite basis obstructions to the actual infinite DPR constant -/

noncomputable section
open scoped ENNReal NNReal

namespace ComplementedSubspace

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem chiDPR_eq_top_of_nnreal_lower_bounds
    (h : ∀ K : ℝ≥0, (K : ℝ≥0∞) ≤ chiDPR Z) : chiDPR Z = ⊤ := by
  by_contra hfinite
  have hle := h ((chiDPR Z).toNNReal + 1)
  rw [← ENNReal.coe_toNNReal hfinite] at hle
  have hle' := ENNReal.coe_le_coe.mp hle
  exact (not_le_of_gt (lt_add_of_pos_right (chiDPR Z).toNNReal
    (by norm_num : (0 : ℝ≥0) < 1))) hle'

theorem le_chiDPR_of_basis_obstruction (K : ℝ≥0)
    (V : Submodule ℝ Z) (hVdim : FiniteDimensional ℝ V) (hV : V ≠ ⊥)
    (h : ∀ (F : Submodule ℝ Z), V ≤ F → FiniteDimensional ℝ F →
      ∀ (m : ℕ) (b : Module.Basis (Fin m) ℝ F),
        (K : ℝ≥0∞) ≤ unconditionalBasisConstant b) :
    (K : ℝ≥0∞) ≤ chiDPR Z := by
  have hlocal : (K : ℝ≥0∞) ≤ lambdaDPR Z V := by
    apply le_iInf
    intro F
    apply le_iInf
    intro hVF
    apply le_iInf
    intro hF
    exact le_iInf fun m => le_iInf fun b => h F hVF hF m b
  exact hlocal.trans (le_iSup_of_le V
    (le_iSup_of_le hVdim (le_iSup_of_le hV le_rfl)))

theorem chiDPR_eq_top_of_basis_obstructions
    (h : ∀ K : ℝ≥0, ∃ V : Submodule ℝ Z,
      ∃ hVdim : FiniteDimensional ℝ V, V ≠ ⊥ ∧
        ∀ (F : Submodule ℝ Z), V ≤ F → FiniteDimensional ℝ F →
          ∀ (m : ℕ) (b : Module.Basis (Fin m) ℝ F),
            (K : ℝ≥0∞) ≤ unconditionalBasisConstant b) :
    chiDPR Z = ⊤ := by
  by_contra hfinite
  let K : ℝ≥0 := (chiDPR Z).toNNReal + 1
  obtain ⟨V, hVdim, hV, hbasis⟩ := h K
  have hle := le_chiDPR_of_basis_obstruction K V hVdim hV hbasis
  rw [← ENNReal.coe_toNNReal hfinite] at hle
  have hle' : K ≤ (chiDPR Z).toNNReal := ENNReal.coe_le_coe.mp hle
  have hlt : (chiDPR Z).toNNReal < K := by
    exact lt_add_of_pos_right _ (by norm_num : (0 : ℝ≥0) < 1)
  exact (not_le_of_gt hlt) hle'

end ComplementedSubspace
