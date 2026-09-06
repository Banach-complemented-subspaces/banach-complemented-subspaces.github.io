import ComplementedSubspace.CorollaryStatement
import ComplementedSubspace.FiniteApproximation
import ComplementedSubspace.FiniteCubeBound

/-!
# An unconditional Schauder basis implies finite DPR

Mathlib's uniform boundedness theorem bounds all finite coordinate projections.
The convex hull of the real sign cube then bounds all real scalar multipliers.
Finite basis spans approximate any finite family, and the finite-rank correction
theorem upgrades approximation to exact finite-dimensional superspaces.
-/

noncomputable section
open scoped BigOperators ENNReal NNReal Topology

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι : Type*}

theorem finite_basis_bound_of_schauder
    (b : UnconditionalSchauderBasis ι ℝ E) {F : Submodule ℝ E} {n : ℕ}
    (c : Module.Basis (Fin n) ℝ F) (e : Fin n → ι) (he : Function.Injective e)
    (hc : ∀ i, (c i : E) = b (e i)) :
    unconditionalBasisConstant c ≤
      ((max 1 (2 * b.nnnormProjBound) : ℝ≥0) : ℝ≥0∞) := by
  classical
  apply max_le (by exact_mod_cast le_max_left (1 : ℝ≥0) (2 * b.nnnormProjBound))
  refine iSup_le fun θ => iSup_le fun hθ => ?_
  apply enorm_le_coe.mpr
  apply NNReal.coe_le_coe.mp
  apply ContinuousLinearMap.opNorm_le_bound _ (NNReal.coe_nonneg _)
  intro z
  have hz : (z : E) = ∑ i, c.repr z i • b (e i) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hc] using
      congrArg (fun y : F => (y : E)) (c.sum_repr z).symm
  have hpart (t : Finset (Fin n)) :
      (∑ i ∈ t, c.repr z i • b (e i)) = b.proj (t.image e) z := by
    rw [hz, map_sum]
    simp only [map_smul, GeneralSchauderBasis.proj_apply_basis_mem]
    have hi (i : Fin n) : e i ∈ t.image e ↔ i ∈ t :=
      Finset.mem_image.trans ⟨fun ⟨j, hj, hji⟩ => he hji ▸ hj,
        fun hi => ⟨i, hi, rfl⟩⟩
    simp only [hi, smul_ite, smul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  have hb (t : Finset (Fin n)) : ‖∑ i ∈ t, c.repr z i • b (e i)‖ ≤
      (b.nnnormProjBound : ℝ) * ‖z‖ := by
    rw [hpart]
    exact ((b.proj (t.image e)).le_opNorm (z : E)).trans
      (mul_le_mul_of_nonneg_right (b.norm_proj_le_nnnormProjBound _) (norm_nonneg z))
  have hm : (basisMultiplier c θ z : E) =
      ∑ i, θ i • (c.repr z i • b (e i)) := by
    change (c.constr ℝ (fun i => θ i • c i) z : E) = _
    rw [Module.Basis.constr_apply_fintype]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hc, smul_smul,
      Module.Basis.equivFun_apply, mul_comm]
  have hbound := norm_sum_smul_le_of_subsum_bound
    (fun i => c.repr z i • b (e i)) ((b.nnnormProjBound : ℝ) * ‖z‖) hb θ hθ
  change ‖(basisMultiplier c θ z : E)‖ ≤ _
  rw [hm]
  calc
    ‖∑ i, θ i • (c.repr z i • b (e i))‖ ≤
        (2 * (b.nnnormProjBound : ℝ)) * ‖z‖ := by simpa only [mul_assoc] using hbound
    _ ≤ ((max 1 (2 * b.nnnormProjBound) : ℝ≥0) : ℝ) * ‖z‖ :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast (le_max_right (1 : ℝ≥0) (2 * b.nnnormProjBound))) (norm_nonneg z)

theorem hasFiniteUnconditionalApproximations_of_schauder
    (b : UnconditionalSchauderBasis ι ℝ E) :
    HasFiniteUnconditionalApproximations E (max 1 (2 * b.nnnormProjBound)) := by
  classical
  intro m x δ hδ
  have hevent (i : Fin m) : ∀ᶠ s : Finset ι in Filter.atTop,
      ‖b.proj s (x i) - x i‖ < δ := by
    have h := (Metric.tendsto_nhds.mp (b.tendsto_proj (x i))) δ hδ
    simpa only [dist_eq_norm, SummationFilter.unconditional_filter] using h
  obtain ⟨s, hs⟩ := (Filter.eventually_all.mpr hevent).exists
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let v : Fin (Fintype.card s) → E := fun i => b (e i).val
  have hli : LinearIndependent ℝ v :=
    b.linearIndependent.comp (fun i => (e i).val)
      (Subtype.val_injective.comp e.injective)
  let F := Submodule.span ℝ (Set.range v)
  let c : Module.Basis (Fin (Fintype.card s)) ℝ F := Module.Basis.span hli
  refine ⟨F, Fintype.card s, c,
    finite_basis_bound_of_schauder b c (fun i => (e i).val)
      (Subtype.val_injective.comp e.injective) (fun i => Module.Basis.coe_span_apply hli i), ?_⟩
  intro i
  have hy : b.proj s (x i) ∈ F := by
    rw [GeneralSchauderBasis.proj_apply]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨e.symm ⟨j, hj⟩, by simp [v]⟩
  exact ⟨⟨b.proj s (x i), hy⟩, (hs i).le⟩

theorem chiDPR_le_of_unconditionalSchauderBasis
    (b : UnconditionalSchauderBasis ι ℝ E) :
    chiDPR E ≤ ((max 1 (2 * b.nnnormProjBound) : ℝ≥0) : ℝ≥0∞) :=
  chiDPR_le_constant_of_finite_approximations _ (le_max_left _ _)
    (hasFiniteUnconditionalApproximations_of_schauder b)

/-- A real unconditional Schauder basis in a Banach space forces finite DPR. -/
theorem hasDPR_of_unconditionalSchauderBasis (b : UnconditionalSchauderBasis ι ℝ E) :
    HasDPRLocalUnconditionalStructure E :=
  hasDPR_of_finite_approximations _ (hasFiniteUnconditionalApproximations_of_schauder b)

theorem not_hasUnconditionalSchauderBasis_of_chiDPR_top (hE : chiDPR E = ⊤) :
    ¬ HasUnconditionalSchauderBasis ℝ E := by
  intro hBasis
  rcases hBasis with hfin | hinf
  · rcases hfin with ⟨n, ⟨b⟩⟩
    have h := hasDPR_of_unconditionalSchauderBasis b
    change chiDPR E < ⊤ at h
    rw [hE] at h
    exact h.false
  · rcases hinf with ⟨b⟩
    have h := hasDPR_of_unconditionalSchauderBasis b
    change chiDPR E < ⊤ at h
    rw [hE] at h
    exact h.false

end ComplementedSubspace
