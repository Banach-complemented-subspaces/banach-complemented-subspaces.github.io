import ComplementedSubspace.LocalHilbertCompactness
import ComplementedSubspace.LocalHilbertCoordinates
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Choose

/-!
The local Hilbert approximation gate, with a dimension-uniform threshold.
The resulting norm satisfies the exact parallelogram law; the final wrapper
turns it into a genuine inner-product norm by Jordan-von Neumann.
-/

noncomputable section

universe u

open Set Filter Topology

namespace ComplementedSubspace

set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual positive-definite seminorm, bounded above by the given norm and
below by its `D`-multiple, satisfying the exact real parallelogram law. -/
def HasHilbertNormWithin (D : ℝ) : Prop :=
  ∃ q : Seminorm ℝ E,
    (∀ x, q x = 0 → x = 0) ∧
    (∀ x y, q (x + y) ^ 2 + q (x - y) ^ 2 = 2 * (q x ^ 2 + q y ^ 2)) ∧
    ∀ x, q x ≤ ‖x‖ ∧ ‖x‖ ≤ D * q x

/-- Data for a positive real norm satisfying the exact parallelogram law. -/
structure HilbertNormModel where
  q : Seminorm ℝ E
  definite : ∀ x, q x = 0 → x = 0
  parallelogram : ∀ x y, q (x + y) ^ 2 + q (x - y) ^ 2 = 2 * (q x ^ 2 + q y ^ 2)

namespace HilbertNormModel

variable {E} (p : HilbertNormModel E)

/-- A type synonym prevents the new norm from replacing the original norm. -/
def Space (_p : HilbertNormModel E) := E

instance : AddCommGroup p.Space := inferInstanceAs (AddCommGroup E)
instance : Module ℝ p.Space := inferInstanceAs (Module ℝ E)

def addGroupNorm : AddGroupNorm p.Space where
  toAddGroupSeminorm := p.q.toAddGroupSeminorm
  eq_zero_of_map_eq_zero' := p.definite

instance : NormedAddCommGroup p.Space := p.addGroupNorm.toNormedAddCommGroup

instance : NormedSpace ℝ p.Space where
  norm_smul_le r x := (p.q.smul' r x).le

@[simp] theorem space_norm (x : p.Space) : ‖x‖ = p.q x := rfl

/-- Mathlib's proved Jordan-von Neumann construction supplies the actual
inner product, with precisely the stored norm. -/
instance : InnerProductSpace ℝ p.Space :=
  InnerProductSpace.ofNorm (𝕜 := ℝ) (fun x y => by
    change p.q (x + y) * p.q (x + y) + p.q (x - y) * p.q (x - y) =
      2 * (p.q x * p.q x + p.q y * p.q y)
    simpa only [pow_two] using p.parallelogram x y)

instance [FiniteDimensional ℝ E] : FiniteDimensional ℝ p.Space :=
  inferInstanceAs (FiniteDimensional ℝ E)

instance [FiniteDimensional ℝ E] : CompleteSpace p.Space :=
  FiniteDimensional.complete ℝ p.Space

/-- The identity map between the original space and the constructed Hilbert
norm, with explicit bounds in both directions. -/
def equivOfBounds (D : ℝ) (hp : ∀ x : E, p.q x ≤ ‖x‖ ∧ ‖x‖ ≤ D * p.q x) :
    E ≃L[ℝ] p.Space :=
  LinearEquiv.toContinuousLinearEquivOfBounds (E := E) (F := p.Space)
    (show E ≃ₗ[ℝ] p.Space from LinearEquiv.refl ℝ E) 1 D
    (fun x => by change p.q x ≤ 1 * ‖x‖; simpa only [one_mul] using (hp x).1)
    (fun x => (hp x).2)

@[simp] theorem equivOfBounds_apply (D : ℝ)
    (hp : ∀ x : E, p.q x ≤ ‖x‖ ∧ ‖x‖ ≤ D * p.q x) (x : E) :
    p.equivOfBounds D hp x = x := rfl

theorem norm_equivOfBounds_le (D : ℝ)
    (hp : ∀ x : E, p.q x ≤ ‖x‖ ∧ ‖x‖ ≤ D * p.q x) :
    ‖(p.equivOfBounds D hp).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change p.q x ≤ 1 * ‖x‖
  simpa only [one_mul] using (hp x).1

theorem norm_equivOfBounds_symm_le {D : ℝ} (hD : 0 ≤ D)
    (hp : ∀ x : E, p.q x ≤ ‖x‖ ∧ ‖x‖ ≤ D * p.q x) :
    ‖(p.equivOfBounds D hp).symm.toContinuousLinearMap‖ ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro x
  exact (hp x).2

end HilbertNormModel

variable {E}

theorem HasHilbertNormWithin.exists_model {D : ℝ} (h : HasHilbertNormWithin E D) :
    ∃ p : HilbertNormModel E, ∀ x : E,
      p.q x ≤ ‖x‖ ∧ ‖x‖ ≤ D * p.q x := by
  obtain ⟨q, hq, hp, hc⟩ := h
  exact ⟨⟨q, hq, hp⟩, hc⟩

/-- Transfer the fixed-coordinate compactness result through uniformly
conditioned coordinates. The intermediate comparison factor is squared, so
the caller can choose its square root to obtain any prescribed distortion. -/
theorem hasHilbertNormWithin_of_normalized_coordinates {d : ℕ} {D ν : ℝ}
    (hD : 0 < D)
    (hν : ∀ q : NormalizedNorm (Fin d → ℝ) 1 d, ApproxParallelogram q ν →
      ∃ h : NormalizedNorm (Fin d → ℝ) 1 d, ApproxParallelogram h 1 ∧
        ∀ x, h x / D ≤ q x ∧ q x ≤ D * h x)
    (e : (Fin d → ℝ) ≃ₗ[ℝ] E)
    (he : ∀ x, ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ (d : ℝ) * ‖x‖)
    (hpar : ApproxParallelogram (fun x : E => ‖x‖) ν) :
    HasHilbertNormWithin E (D ^ 2) := by
  let q : NormalizedNorm (Fin d → ℝ) 1 d := ⟨fun x => ‖e x‖,
    ⟨(by intro x y; simpa only [map_add] using norm_add_le (e x) (e y)),
    (by intro r x; simp only [map_smul, norm_smul, Real.norm_eq_abs]),
    (by intro x; simpa only [one_mul] using (he x).1), fun x => (he x).2⟩⟩
  have hq : ApproxParallelogram q ν := by
    intro x y
    simpa only [q, map_add, map_sub] using hpar (e x) (e y)
  obtain ⟨h, hh, hcomp⟩ := hν q hq
  let p : Seminorm ℝ E := Seminorm.of (fun x => h (e.symm x) / D)
    (by
      intro x y
      rw [map_add]
      exact (div_le_div_of_nonneg_right (h.property.1 _ _) hD.le).trans_eq (add_div _ _ _))
    (by
      intro r x
      rw [map_smul, h.smul, Real.norm_eq_abs]
      ring)
  refine ⟨p, ?_, ?_, ?_⟩
  · intro x hx
    have hz : h (e.symm x) = 0 := (div_eq_zero_iff).mp hx |>.resolve_right hD.ne'
    have hl := h.lower (e.symm x)
    rw [hz, one_mul] at hl
    have hez : e.symm x = 0 := norm_eq_zero.mp (le_antisymm hl (norm_nonneg _))
    simpa using congrArg e hez
  · intro x y
    have hp := h.parallelogram_of_one hh (e.symm x) (e.symm y)
    change (h (e.symm (x + y)) / D) ^ 2 + (h (e.symm (x - y)) / D) ^ 2 =
      2 * ((h (e.symm x) / D) ^ 2 + (h (e.symm y) / D) ^ 2)
    rw [map_add, map_sub]
    field_simp [hD.ne']
    nlinarith
  · intro x
    have hc := hcomp (e.symm x)
    change h (e.symm x) / D ≤ ‖e (e.symm x)‖ ∧
      ‖e (e.symm x)‖ ≤ D * h (e.symm x) at hc
    rw [e.apply_symm_apply] at hc
    refine ⟨hc.1, hc.2.trans_eq ?_⟩
    change D * h (e.symm x) = D ^ 2 * (h (e.symm x) / D)
    field_simp [hD.ne']

/-- For a fixed dimension, sufficiently small parallelogram defect gives any
prescribed Hilbert distortion, uniformly over all norms and all carriers. -/
theorem exists_localHilbert_threshold_finrank (d : ℕ) {D : ℝ} (hD : 1 < D) :
    ∃ ν > 1, ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ F], Module.finrank ℝ F = d →
      ApproxParallelogram (fun x : F => ‖x‖) ν → HasHilbertNormWithin F D := by
  have hDsqrt : 1 < Real.sqrt D := by
    have := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) hD
    simpa only [Real.sqrt_one] using this
  obtain ⟨ν, hν, hcoord⟩ :=
    normalizedNorm_local_hilbert (E := Fin d → ℝ) (a := 1) (b := d)
      (D := Real.sqrt D) (by norm_num) hDsqrt
  refine ⟨ν, hν, ?_⟩
  intro F _ _ _ hdim hpar
  obtain ⟨e, he⟩ := exists_normalized_coordinates (Module.finBasisOfFinrankEq ℝ F hdim)
  have h := hasHilbertNormWithin_of_normalized_coordinates
    (by linarith : 0 < Real.sqrt D) hcoord e (by simpa using he) hpar
  simpa only [Real.sq_sqrt (show 0 ≤ D by linarith)] using h

/-- The qualitative replacement for the quantitative approximate
Jordan-von Neumann theorem used in the manuscript. The threshold depends only
on an upper bound for dimension and on the requested distortion. -/
theorem exists_localHilbert_threshold (k : ℕ) {D : ℝ} (hD : 1 < D) :
    ∃ ν > 1, ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ F], Module.finrank ℝ F ≤ k →
      ApproxParallelogram (fun x : F => ‖x‖) ν → HasHilbertNormWithin F D := by
  classical
  choose ν hν hgood using fun d : Fin (k + 1) =>
    exists_localHilbert_threshold_finrank.{u} d.val hD
  let μ : ℝ := Finset.univ.inf' (by simp) ν
  have hμ : 1 < μ := by
    exact (Finset.lt_inf'_iff _).mpr (fun d _ => hν d)
  refine ⟨μ, hμ, ?_⟩
  intro F _ _ _ hdim hpar
  let d : Fin (k + 1) := ⟨Module.finrank ℝ F, Nat.lt_succ_of_le hdim⟩
  apply hgood d F rfl
  exact hpar.mono (Finset.inf'_le ν (Finset.mem_univ d))

/-- The form consumed by the infinite-sum construction: ambient dimension is
unrestricted, while every subspace up to dimension `k` shares one threshold. -/
theorem exists_localHilbert_subspace_threshold (k : ℕ) {D : ℝ} (hD : 1 < D) :
    ∃ ν > 1, ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F],
      ApproxParallelogram (fun x : F => ‖x‖) ν →
      ∀ (S : Submodule ℝ F) [FiniteDimensional ℝ S], Module.finrank ℝ S ≤ k →
        HasHilbertNormWithin S D := by
  obtain ⟨ν, hν, hgood⟩ := exists_localHilbert_threshold.{u} k hD
  refine ⟨ν, hν, ?_⟩
  intro F _ _ hpar S _ hdim
  exact hgood S hdim (hpar.subspace S)

end ComplementedSubspace
