import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
Uniform coordinates for finite dimensional norms, obtained by maximizing a
determinant on a product of closed balls. This is the elementary finite
dimensional argument behind an Auerbach basis; no ellipsoid theorem is used.
-/

noncomputable section

open Set Filter Topology
open scoped BigOperators

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A determinant-maximizing basis in a ball has coordinate functionals bounded
by the reciprocal radius. The maximization uses only finite-dimensional
compactness. -/
theorem exists_bounded_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι ℝ E) :
    ∃ (R : ℝ) (b : Module.Basis ι ℝ E), 0 < R ∧
      (∀ i, ‖b i‖ ≤ R) ∧ (∀ x i, |b.repr x i| * R ≤ ‖x‖) := by
  classical
  let R : ℝ := (∑ i, ‖e i‖) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let K : Set (ι → E) := Set.pi Set.univ (fun _ => Metric.closedBall 0 R)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall 0 R
  have heK : (e : ι → E) ∈ K := by
    intro i _
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (Finset.single_le_sum (fun j _ => norm_nonneg (e j))
      (Finset.mem_univ i)).trans (by dsimp [R]; linarith)
  have hdet : Continuous (fun v : ι → E => |e.det v|) := by
    change Continuous (fun v : ι → E => |(e.toMatrix v).det|)
    apply Continuous.abs
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply i).comp (e.equivFunL.continuous.comp (continuous_apply j))
  obtain ⟨v, hvK, hvmax⟩ := hK.exists_isMaxOn ⟨e, heK⟩ hdet.continuousOn
  have hvdet : e.det v ≠ 0 := by
    have hm : |e.det e| ≤ |e.det v| := hvmax heK
    rw [e.det_self, abs_one] at hm
    exact fun hz => by norm_num [hz] at hm
  obtain ⟨hvli, hvsp⟩ := (e.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hvdet)
  let b : Module.Basis ι ℝ E := Module.Basis.mk hvli hvsp.ge
  have hcoord (x : E) (i : ι) :
      e.det v * b.repr x i = e.det (Function.update v i x) := by
    have hh := congrArg (fun f : E →ₗ[ℝ] ℝ => f x)
      (e.det_smul_mk_coord_eq_det_update hvli hvsp.ge i)
    exact hh
  have hball (x : E) (hx : ‖x‖ ≤ R) (i : ι) : |b.repr x i| ≤ 1 := by
    have hupdate : Function.update v i x ∈ K := by
      intro j _
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self, Metric.mem_closedBall, dist_zero_right] using hx
      · simpa only [Function.update_of_ne hj] using hvK j (mem_univ j)
    have hm : |e.det (Function.update v i x)| ≤ |e.det v| := hvmax hupdate
    rw [← hcoord x i, abs_mul] at hm
    exact (mul_le_mul_iff_right₀ (abs_pos.mpr hvdet)).mp
      (by simpa only [mul_comm, one_mul, mul_one] using hm)
  refine ⟨R, b, hR, ?_, ?_⟩
  · intro i
    simpa only [b, Module.Basis.coe_mk, Metric.mem_closedBall, dist_zero_right]
      using hvK i (mem_univ i)
  · intro x i
    by_cases hx : x = 0
    · simp [hx]
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hn : ‖(R / ‖x‖) • x‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hxn)]
      exact le_of_eq (div_mul_cancel₀ R hxn.ne')
    have hh := hball ((R / ‖x‖) • x) hn i
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (div_pos hR hxn)] at hh
    have := (mul_le_mul_of_nonneg_right hh hxn.le)
    field_simp at this
    nlinarith

/-- Uniform coordinates: the lower comparison is one and the upper comparison
depends only on the number of coordinates, independently of the original
norm. This includes the zero-dimensional case. -/
theorem exists_normalized_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e₀ : Module.Basis ι ℝ E) :
    ∃ e : (ι → ℝ) ≃ₗ[ℝ] E, ∀ x, ‖x‖ ≤ ‖e x‖ ∧
      ‖e x‖ ≤ (Fintype.card ι : ℝ) * ‖x‖ := by
  classical
  obtain ⟨R, b, hR, hb, hcoord⟩ := exists_bounded_basis e₀
  let c := b.equivFun.symm
  let e : (ι → ℝ) ≃ₗ[ℝ] E :=
    c.trans (LinearEquiv.smulOfNeZero ℝ E R⁻¹ (inv_ne_zero hR.ne'))
  refine ⟨e, fun x => ?_⟩
  have hscale : ‖e x‖ * R = ‖c x‖ := by
    change ‖R⁻¹ • c x‖ * R = ‖c x‖
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    field_simp
  have hc_repr : b.equivFun (c x) = x := b.equivFun.apply_symm_apply x
  have hlow : ‖x‖ * R ≤ ‖c x‖ := by
    apply (le_div_iff₀ hR).mp
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg _) hR.le)).mpr
    intro i
    have hi := hcoord (c x) i
    have heq : b.repr (c x) i = x i := congrFun hc_repr i
    rw [heq] at hi
    simpa only [Real.norm_eq_abs] using (le_div_iff₀ hR).mpr hi
  have hexp : c x = ∑ i, x i • b i := by
    symm
    simpa only [hc_repr] using b.sum_equivFun (c x)
  have hupp : ‖c x‖ ≤ (Fintype.card ι : ℝ) * ‖x‖ * R := by
    rw [hexp]
    calc
      ‖∑ i, x i • b i‖ ≤ ∑ i, ‖x i • b i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, ‖x‖ * R := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm x i) (hb i) (norm_nonneg _) (norm_nonneg _)
      _ = (Fintype.card ι : ℝ) * ‖x‖ * R := by simp; ring
  constructor <;> nlinarith

end ComplementedSubspace
