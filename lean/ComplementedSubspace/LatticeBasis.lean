import ComplementedSubspace.LatticeSpectral
import ComplementedSubspace.LocalUnconditional

/-! # The inherited norm on a finite disjoint span is 1-unconditional -/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E]

theorem unconditionalBasisConstant_le_one_of_disjoint {F : Submodule ℝ E}
    {n : ℕ} (b : Module.Basis (Fin n) ℝ F)
    (hdis : Pairwise fun i j => IsVLDisjoint (b i : E) (b j : E)) :
    unconditionalBasisConstant b ≤ 1 := by
  apply max_le le_rfl
  refine iSup_le fun θ => iSup_le fun hθ => ?_
  apply enorm_le_coe.mpr
  apply NNReal.coe_le_coe.mp
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  have hsum : (z : E) = ∑ i, b.repr z i • (b i : E) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
      congrArg (fun y : F => (y : E)) (b.sum_repr z).symm
  have hmult : (basisMultiplier b θ z : E) =
      ∑ i, (θ i * b.repr z i) • (b i : E) := by
    change (b.constr ℝ (fun i => θ i • b i) z : E) = _
    rw [Module.Basis.constr_apply_fintype]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, smul_smul, mul_comm,
      Module.Basis.equivFun_apply]
  have habs : |(basisMultiplier b θ z : E)| ≤ |(z : E)| := by
    rw [hmult, hsum, abs_sum_of_pairwise_isVLDisjoint hdis,
      abs_sum_of_pairwise_isVLDisjoint hdis]
    apply Finset.sum_le_sum
    intro i _
    apply smul_le_smul_of_nonneg_right _ (abs_nonneg _)
    rw [abs_mul]
    have hi : |θ i| ≤ 1 := by simpa only [Real.norm_eq_abs] using hθ i
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (abs_nonneg (b.repr z i))
  simpa only [one_mul, Submodule.norm_coe] using norm_le_norm_of_abs_le_abs habs

/-- Remove zero cells and reindex the remaining disjoint family to obtain a
basis of exactly its original linear span. No change of norm is made. -/
theorem exists_unconditional_basis_of_disjoint {ι : Type*} [Fintype ι]
    (v : ι → E) (hdis : Pairwise fun i j => IsVLDisjoint (v i) (v j)) :
    ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℝ (Submodule.span ℝ (Set.range v)),
      unconditionalBasisConstant b ≤ 1 := by
  classical
  let J := {i : ι // v i ≠ 0}
  let n := Fintype.card J
  let e : Fin n ≃ J := (Fintype.equivFin J).symm
  let w : Fin n → E := fun i => v (e i).val
  have hw0 : ∀ i, w i ≠ 0 := fun i => (e i).property
  have hwd : Pairwise fun i j => IsVLDisjoint (w i) (w j) := by
    intro i j hij
    apply hdis
    intro heq
    exact hij (e.injective (Subtype.ext heq))
  have hli : LinearIndependent ℝ w :=
    linearIndependent_of_pairwise_isVLDisjoint hw0 hwd
  have hspan : Submodule.span ℝ (Set.range w) = Submodule.span ℝ (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self (e i).val)
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      by_cases hi : v i = 0
      · rw [hi]; exact Submodule.zero_mem _
      · have heq : w (e.symm ⟨i, hi⟩) = v i := by simp only [w, e.apply_symm_apply]
        rw [← heq]
        exact Submodule.subset_span (Set.mem_range_self _)
  let b : Module.Basis (Fin n) ℝ (Submodule.span ℝ (Set.range v)) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  refine ⟨n, b, unconditionalBasisConstant_le_one_of_disjoint b ?_⟩
  simpa only [b, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply] using hwd

theorem LatticeBandPartition.exists_unconditional_basis
    (P : LatticeBandPartition E) (u : E) :
    ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℝ (P.cellSpan u),
      unconditionalBasisConstant b ≤ 1 :=
  exists_unconditional_basis_of_disjoint _ (P.pairwise_disjoint u)

end ComplementedSubspace
