import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
Compactness of norms with fixed comparison constants.  All norms in the family
are functions on the same reference normed space.  The lower comparison bound
is essential: it prevents a limiting norm from degenerating.
-/

noncomputable section

open Set Filter Topology

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A seminorm presented as a real function, with uniform comparison bounds. -/
def IsNormalizedNorm (a b : ℝ) (q : E → ℝ) : Prop :=
  (∀ x y, q (x + y) ≤ q x + q y) ∧
  (∀ (r : ℝ) x, q (r • x) = |r| * q x) ∧
  (∀ x, a * ‖x‖ ≤ q x) ∧ (∀ x, q x ≤ b * ‖x‖)

/-- The pointwise topology on a family of uniformly equivalent norms. -/
def NormalizedNorm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) := {q : E → ℝ // IsNormalizedNorm a b q}

instance (a b : ℝ) : TopologicalSpace (NormalizedNorm E a b) :=
  inferInstanceAs (TopologicalSpace {q : E → ℝ // IsNormalizedNorm a b q})

instance (a b : ℝ) : CoeFun (NormalizedNorm E a b) (fun _ => E → ℝ) :=
  ⟨fun q => q.val⟩

namespace NormalizedNorm

variable {a b : ℝ}

def toSeminorm (q : NormalizedNorm E a b) : Seminorm ℝ E :=
  Seminorm.of q q.property.1 (by simpa only [Real.norm_eq_abs] using q.property.2.1)

@[simp] theorem toSeminorm_apply (q : NormalizedNorm E a b) (x : E) :
    q.toSeminorm x = q x := rfl

@[simp] theorem map_zero (q : NormalizedNorm E a b) : q 0 = 0 :=
  _root_.map_zero q.toSeminorm

theorem nonneg (q : NormalizedNorm E a b) (x : E) : 0 ≤ q x :=
  apply_nonneg q.toSeminorm x

theorem lower (q : NormalizedNorm E a b) (x : E) : a * ‖x‖ ≤ q x :=
  q.property.2.2.1 x

theorem upper (q : NormalizedNorm E a b) (x : E) : q x ≤ b * ‖x‖ :=
  q.property.2.2.2 x

theorem smul (q : NormalizedNorm E a b) (r : ℝ) (x : E) :
    q (r • x) = |r| * q x := q.property.2.1 r x

theorem abs_sub_le (q : NormalizedNorm E a b) (x y : E) :
    |q x - q y| ≤ b * ‖x - y‖ := by
  have hxy := q.property.1 (x - y) y
  have hyx := q.property.1 (y - x) x
  have hu := q.upper (x - y)
  have hv := q.upper (y - x)
  rw [norm_sub_rev] at hv
  simp only [sub_add_cancel] at hxy hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem continuous_eval (x : E) : Continuous (fun q : NormalizedNorm E a b => q x) :=
  (continuous_apply x).comp continuous_subtype_val

/-- Pointwise convergence becomes joint continuity because all members have
the same Lipschitz constant. -/
theorem continuous_joint_eval :
    Continuous (fun p : NormalizedNorm E a b × E => p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun z : NormalizedNorm E a b × E => by
      have hz : dist (z.1 z.2) (z.1 p.2) ≤ b * ‖z.2 - p.2‖ := by
        simpa only [Real.dist_eq] using NormalizedNorm.abs_sub_le z.1 z.2 p.2
      exact (dist_triangle (z.1 z.2) (z.1 p.2) (p.1 p.2)).trans (add_le_add hz le_rfl))
  have ht : Tendsto (fun z : NormalizedNorm E a b × E =>
      b * ‖z.2 - p.2‖ + dist (z.1 p.2) (p.1 p.2)) (𝓝 p) (𝓝 0) := by
    have hc : Continuous (fun z : NormalizedNorm E a b × E =>
        b * ‖z.2 - p.2‖ + dist (z.1 p.2) (p.1 p.2)) := by
      apply Continuous.add
      · fun_prop
      · exact ((continuous_eval p.2).comp continuous_fst).dist continuous_const
    simpa only [sub_self, norm_zero, mul_zero, dist_self, add_zero] using hc.tendsto p
  exact ht

end NormalizedNorm

theorem isClosed_isNormalizedNorm (a b : ℝ) :
    IsClosed {q : E → ℝ | IsNormalizedNorm a b q} := by
  unfold IsNormalizedNorm
  simp only [setOf_and, setOf_forall]
  refine (isClosed_iInter fun x => isClosed_iInter fun y => ?_).inter
    ((isClosed_iInter fun r => isClosed_iInter fun x => ?_).inter
    ((isClosed_iInter fun x => ?_).inter (isClosed_iInter fun x => ?_)))
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · exact isClosed_eq (continuous_apply _) (continuous_const.mul (continuous_apply _))
  · exact isClosed_le continuous_const (continuous_apply _)
  · exact isClosed_le (continuous_apply _) continuous_const

theorem isCompact_isNormalizedNorm (a b : ℝ) :
    IsCompact {q : E → ℝ | IsNormalizedNorm a b q} := by
  apply (isCompact_univ_pi fun x : E =>
    (isCompact_Icc : IsCompact (Icc (a * ‖x‖) (b * ‖x‖)))).of_isClosed_subset
      (isClosed_isNormalizedNorm a b)
  intro q hq x _
  exact ⟨hq.2.2.1 x, hq.2.2.2 x⟩

instance (a b : ℝ) : CompactSpace (NormalizedNorm E a b) :=
  isCompact_iff_compactSpace.mp (isCompact_isNormalizedNorm a b)

/-- The one-sided parallelogram condition used in the construction. -/
def ApproxParallelogram (q : E → ℝ) (ν : ℝ) : Prop :=
  ∀ x y, q (x + y) ^ 2 + q (x - y) ^ 2 ≤ 2 * ν * (q x ^ 2 + q y ^ 2)

theorem isClosed_approxParallelogram (a b ν : ℝ) :
    IsClosed {q : NormalizedNorm E a b | ApproxParallelogram q ν} := by
  simp only [ApproxParallelogram, setOf_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_le ((NormalizedNorm.continuous_eval _).pow 2 |>.add
      ((NormalizedNorm.continuous_eval _).pow 2))
      (continuous_const.mul ((NormalizedNorm.continuous_eval _).pow 2 |>.add
        ((NormalizedNorm.continuous_eval _).pow 2)))

theorem ApproxParallelogram.mono {q : E → ℝ} {ν μ : ℝ}
    (h : ApproxParallelogram q ν) (hνμ : ν ≤ μ) : ApproxParallelogram q μ := by
  intro x y
  exact (h x y).trans (by gcongr)

/-- The norm inequality restricts to every linear subspace without changing
its constant. -/
theorem ApproxParallelogram.subspace {ν : ℝ}
    (h : ApproxParallelogram (fun x : E => ‖x‖) ν) (S : Submodule ℝ E) :
    ApproxParallelogram (fun x : S => ‖x‖) ν := by
  intro x y
  exact h (x : E) (y : E)

/-- At constant one, the reverse inequality follows by the substitution
`(x,y) ↦ (x+y,x-y)`; hence the inequality is the exact parallelogram law. -/
theorem NormalizedNorm.parallelogram_of_one {a b : ℝ} (q : NormalizedNorm E a b)
    (h : ApproxParallelogram q 1) (x y : E) :
    q (x + y) ^ 2 + q (x - y) ^ 2 = 2 * (q x ^ 2 + q y ^ 2) := by
  have h₁ := h x y
  have h₂ := h (x + y) (x - y)
  have hx : (x + y) + (x - y) = (2 : ℝ) • x := by module
  have hy : (x + y) - (x - y) = (2 : ℝ) • y := by module
  rw [hx, hy, q.smul, q.smul] at h₂
  norm_num at h₁ h₂
  nlinarith

/-- A compact family of normalized norms has a uniform approximate
parallelogram threshold for every open neighborhood of its exact members. -/
theorem normalizedNorm_uniform_threshold {a b : ℝ}
    (U : Set (NormalizedNorm E a b)) (hU : IsOpen U)
    (hExact : ∀ q : NormalizedNorm E a b, ApproxParallelogram q 1 → q ∈ U) :
    ∃ ν > 1, ∀ q : NormalizedNorm E a b, ApproxParallelogram q ν → q ∈ U := by
  let V : Ioi (1 : ℝ) → Set (NormalizedNorm E a b) :=
    fun ν => {q | ApproxParallelogram q ν.val}
  have hdir : Directed (· ⊇ ·) V := by
    intro ν μ
    refine ⟨⟨min ν.val μ.val, (show 1 < min ν.val μ.val from
      lt_min ν.property μ.property)⟩, ?_, ?_⟩
    · intro q hq
      exact hq.mono (min_le_left _ _)
    · intro q hq
      exact hq.mono (min_le_right _ _)
  have hclosed : ∀ ν, IsClosed (V ν) :=
    fun ν => isClosed_approxParallelogram a b ν.val
  have hsub : (⋂ ν, V ν) ⊆ U := by
    intro q hq
    apply hExact q
    intro x y
    have hlim : Tendsto (fun ν : ℝ => 2 * ν * (q x ^ 2 + q y ^ 2))
        (𝓝[>] 1) (𝓝 (2 * (q x ^ 2 + q y ^ 2))) := by
      have hc : Continuous (fun ν : ℝ => 2 * ν * (q x ^ 2 + q y ^ 2)) := by fun_prop
      simpa only [mul_one] using (hc.tendsto 1).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
    have hh : q (x + y) ^ 2 + q (x - y) ^ 2 ≤ 2 * (q x ^ 2 + q y ^ 2) := by
      apply ge_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with ν hν
      exact (mem_iInter.mp hq ⟨ν, hν⟩) x y
    simpa only [mul_one] using hh
  obtain ⟨ν, hν⟩ := exists_subset_nhds_of_compactSpace hdir hclosed
    (hU.mem_nhdsSet.mpr hsub)
  exact ⟨ν.val, ν.property, fun q hq => hν hq⟩

namespace NormalizedNorm

variable {a b D : ℝ}

/-- Strict comparison on the reference unit sphere. -/
def SphereComparable (h q : NormalizedNorm E a b) (D : ℝ) : Prop :=
  ∀ x : Metric.sphere (0 : E) 1, h x / D < q x ∧ q x < D * h x

theorem isOpen_sphereComparable [FiniteDimensional ℝ E]
    (h : NormalizedNorm E a b) (D : ℝ) :
    IsOpen {q : NormalizedNorm E a b | SphereComparable h q D} := by
  let K := Metric.sphere (0 : E) 1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  have hc : Continuous (fun p : NormalizedNorm E a b × K => p.1 p.2) :=
    continuous_joint_eval.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hh : Continuous (fun p : NormalizedNorm E a b × K => h p.2) :=
    continuous_joint_eval.comp (continuous_const.prodMk (continuous_subtype_val.comp continuous_snd))
  have hf : IsClosed {p : NormalizedNorm E a b × K |
      p.1 p.2 ≤ h p.2 / D ∨ D * h p.2 ≤ p.1 p.2} :=
    (isClosed_le hc (hh.div_const D)).union (isClosed_le (continuous_const.mul hh) hc)
  have hp := isClosedMap_fst_of_compactSpace _ hf
  convert hp.isOpen_compl using 1
  ext q
  simp [SphereComparable, Set.mem_image, Prod.exists, not_or, not_le, K]

theorem sphereComparable_self {a b : ℝ} (ha : 0 < a) (h : NormalizedNorm E a b)
    {D : ℝ} (hD : 1 < D) : SphereComparable h h D := by
  intro x
  have hxn : ‖(x : E)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hh : 0 < h x := by have := h.lower x; rw [hxn, mul_one] at this; linarith
  constructor
  · exact (div_lt_iff₀ (by linarith : 0 < D)).mpr (by nlinarith)
  · nlinarith

/-- Homogeneity promotes comparison on the compact unit sphere to the whole
vector space. Non-strict bounds include the zero vector automatically. -/
theorem SphereComparable.global {a b D : ℝ} {h q : NormalizedNorm E a b}
    (hcomp : SphereComparable h q D) (x : E) :
    h x / D ≤ q x ∧ q x ≤ D * h x := by
  by_cases hx : x = 0
  · simp [hx]
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : Metric.sphere (0 : E) 1 := ⟨‖x‖⁻¹ • x, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hxn, inv_mul_cancel₀ hxn.ne']⟩
  have hh := hcomp y
  change h (‖x‖⁻¹ • x) / D < q (‖x‖⁻¹ • x) ∧
    q (‖x‖⁻¹ • x) < D * h (‖x‖⁻¹ • x) at hh
  rw [h.smul, q.smul, abs_inv, abs_of_pos hxn] at hh
  constructor
  · have := mul_le_mul_of_nonneg_left hh.1.le hxn.le
    simpa only [← mul_div_assoc, ← mul_assoc, mul_inv_cancel₀ hxn.ne', one_mul] using this
  · have := mul_le_mul_of_nonneg_left hh.2.le hxn.le
    have heq : ‖x‖ * (D * (‖x‖⁻¹ * h x)) = D * h x := by
      rw [mul_left_comm ‖x‖ D, ← mul_assoc ‖x‖ ‖x‖⁻¹, mul_inv_cancel₀ hxn.ne', one_mul]
    rw [heq] at this
    simpa only [← mul_assoc, mul_inv_cancel₀ hxn.ne', one_mul] using this

end NormalizedNorm

/-- The qualitative local Hilbert gate in a fixed normalized coordinate
family. The chosen exact norm retains the same nondegeneracy bounds. -/
theorem normalizedNorm_local_hilbert [FiniteDimensional ℝ E]
    {a b D : ℝ} (ha : 0 < a) (hD : 1 < D) :
    ∃ ν > 1, ∀ q : NormalizedNorm E a b, ApproxParallelogram q ν →
      ∃ h : NormalizedNorm E a b, ApproxParallelogram h 1 ∧
        ∀ x, h x / D ≤ q x ∧ q x ≤ D * h x := by
  let U : Set (NormalizedNorm E a b) := {q | ∃ h : NormalizedNorm E a b,
    ApproxParallelogram h 1 ∧ NormalizedNorm.SphereComparable h q D}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    rintro q ⟨h, hh, hcomp⟩
    filter_upwards [(NormalizedNorm.isOpen_sphereComparable h D).mem_nhds hcomp] with q' hq'
    exact ⟨h, hh, hq'⟩
  obtain ⟨ν, hν, hgood⟩ := normalizedNorm_uniform_threshold U hU (by
    intro q hq
    exact ⟨q, hq, NormalizedNorm.sphereComparable_self ha q hD⟩)
  refine ⟨ν, hν, ?_⟩
  intro q hq
  obtain ⟨h, hh, hcomp⟩ := hgood q hq
  exact ⟨h, hh, hcomp.global⟩

end ComplementedSubspace
