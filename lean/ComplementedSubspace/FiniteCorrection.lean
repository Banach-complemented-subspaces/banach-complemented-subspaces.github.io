import ComplementedSubspace.LocalUnconditional
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite-rank corrections of approximate containment

The manuscript uses approximation by finite coordinate or disjoint spans in
several places. This module supplies the common correction argument: extend
the coordinate functionals of a finite basis by Hahn--Banach and add the
finite-rank map sending each basis vector to its approximation error.
Small operator-norm error gives an actual ambient automorphism, with bounds
on both the automorphism and its inverse in the original norm.
-/

noncomputable section
open scoped BigOperators

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite-rank map with prescribed coefficient functionals and errors. -/
def finiteRankCorrection (φ : ι → E →L[ℝ] ℝ) (d : ι → E) : E →L[ℝ] E :=
  ∑ i, (φ i).smulRight (d i)

@[simp] theorem finiteRankCorrection_apply (φ : ι → E →L[ℝ] ℝ)
    (d : ι → E) (x : E) :
    finiteRankCorrection φ d x = ∑ i, φ i x • d i := by
  simp [finiteRankCorrection]

theorem norm_finiteRankCorrection_le (φ : ι → E →L[ℝ] ℝ) (d : ι → E) :
    ‖finiteRankCorrection φ d‖ ≤ ∑ i, ‖φ i‖ * ‖d i‖ := by
  calc
    ‖finiteRankCorrection φ d‖ ≤ ∑ i, ‖(φ i).smulRight (d i)‖ := norm_sum_le _ _
    _ = _ := by simp only [ContinuousLinearMap.norm_smulRight_apply]

/-- Extended coordinates reproduce the prescribed errors on basis vectors. -/
theorem finiteRankCorrection_apply_basis (φ : ι → E →L[ℝ] ℝ)
    (v d : ι → E) (hφ : ∀ i j, φ i (v j) = if i = j then 1 else 0)
    (j : ι) : finiteRankCorrection φ d (v j) = d j := by
  classical
  simp [finiteRankCorrection_apply, hφ]

/-- Coordinates of any finite basis extend continuously to the ambient space,
without increasing their individual norms. -/
theorem exists_extended_basis_coordinates (V : Submodule ℝ E)
    (b : Module.Basis ι ℝ V) :
    ∃ φ : ι → E →L[ℝ] ℝ,
      (∀ i (x : V), φ i (x : E) = b.equivFun x i) ∧
      (∀ i, ‖φ i‖ = ‖(ContinuousLinearMap.proj i).comp
        b.equivFunL.toContinuousLinearMap‖) := by
  classical
  have h i := exists_extension_norm_eq V
    ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  choose φ hφ hnorm using h
  exact ⟨φ, hφ, hnorm⟩

section Complete
variable [CompleteSpace E]

/-- The genuine automorphism `id + U` when the error has norm less than one. -/
def smallPerturbationEquiv (U : E →L[ℝ] E) (hU : ‖U‖ < 1) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit (Units.oneSub (-U) (by simpa using hU))

@[simp] theorem smallPerturbationEquiv_apply (U : E →L[ℝ] E)
    (hU : ‖U‖ < 1) (x : E) : smallPerturbationEquiv U hU x = x + U x := by
  change (1 - -U : E →L[ℝ] E) x = _
  simp

theorem norm_smallPerturbationEquiv_le (U : E →L[ℝ] E) (hU : ‖U‖ < 1) :
    ‖(smallPerturbationEquiv U hU).toContinuousLinearMap‖ ≤ 1 + ‖U‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  simpa [add_mul] using
    (norm_add_le x (U x)).trans (add_le_add_right (U.le_opNorm x) ‖x‖)

theorem smallPerturbationEquiv_lower_bound (U : E →L[ℝ] E)
    (hU : ‖U‖ < 1) (x : E) :
    (1 - ‖U‖) * ‖x‖ ≤ ‖smallPerturbationEquiv U hU x‖ := by
  have h := norm_sub_le (x + U x) (U x)
  have hu := U.le_opNorm x
  simp only [add_sub_cancel_right] at h
  rw [smallPerturbationEquiv_apply]
  nlinarith

theorem norm_smallPerturbationEquiv_symm_le (U : E →L[ℝ] E)
    (hU : ‖U‖ < 1) :
    ‖(smallPerturbationEquiv U hU).symm.toContinuousLinearMap‖ ≤ (1 - ‖U‖)⁻¹ := by
  have hp : 0 < 1 - ‖U‖ := sub_pos.mpr hU
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hp.le)
  intro x
  have h := smallPerturbationEquiv_lower_bound U hU
    ((smallPerturbationEquiv U hU).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact (le_inv_mul_iff₀ hp).mpr h

/-- A finite list of approximate basis vectors is the exact image of the
original list under a controlled automorphism. The hypothesis is the sum of
the coordinate-functional norms times the approximation errors. -/
theorem exists_equiv_of_weighted_errors (φ : ι → E →L[ℝ] ℝ)
    (v w : ι → E) (hφ : ∀ i j, φ i (v j) = if i = j then 1 else 0)
    {ε : ℝ} (hε : ε < 1)
    (herr : (∑ i, ‖φ i‖ * ‖w i - v i‖) ≤ ε) :
    ∃ T : E ≃L[ℝ] E, (∀ i, T (v i) = w i) ∧
      ‖T.toContinuousLinearMap‖ ≤ 1 + ε ∧
      ‖T.symm.toContinuousLinearMap‖ ≤ (1 - ε)⁻¹ := by
  let U := finiteRankCorrection φ (fun i => w i - v i)
  have hu : ‖U‖ ≤ ε := (norm_finiteRankCorrection_le φ _).trans herr
  have hu1 : ‖U‖ < 1 := hu.trans_lt hε
  refine ⟨smallPerturbationEquiv U hu1, ?_, ?_, ?_⟩
  · intro i
    rw [smallPerturbationEquiv_apply]
    change v i + finiteRankCorrection φ (fun i => w i - v i) (v i) = w i
    rw [finiteRankCorrection_apply_basis φ v _ hφ]
    abel
  · exact (norm_smallPerturbationEquiv_le U hu1).trans (by linarith)
  · exact (norm_smallPerturbationEquiv_symm_le U hu1).trans
      (inv_anti₀ (sub_pos.mpr hε) (by linarith))

end Complete
end ComplementedSubspace
