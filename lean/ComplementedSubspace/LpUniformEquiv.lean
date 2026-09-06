import Mathlib.Analysis.Normed.Lp.lpHolder

/-! Uniform coordinate equivalences give an actual equivalence of dependent
lp spaces. The forward and inverse bounds are unchanged. -/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {ι 𝕜 : Type*} {E F : ι → Type*} [NontriviallyNormedField 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

/-- Coordinatewise equivalences with uniform operator bounds, lifted to the
actual dependent lp norms. In particular this applies to outer exponent two. -/
def lpUniformEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : ∀ i, E i ≃L[𝕜] F i) {C D : ℝ}
    (hC : 0 ≤ C) (he : ∀ i, ‖(e i).toContinuousLinearMap‖ ≤ C)
    (hD : 0 ≤ D) (hei : ∀ i, ‖(e i).symm.toContinuousLinearMap‖ ≤ D) :
    lp E p ≃L[𝕜] lp F p := by
  refine ContinuousLinearEquiv.equivOfInverse
    (lp.mapCLM p (fun i => (e i).toContinuousLinearMap) hC he)
    (lp.mapCLM p (fun i => (e i).symm.toContinuousLinearMap) hD hei) ?_ ?_
  · intro x
    ext i
    change (e i).symm (e i (x i)) = x i
    exact (e i).symm_apply_apply (x i)
  · intro x
    ext i
    change e i ((e i).symm (x i)) = x i
    exact (e i).apply_symm_apply (x i)

@[simp] theorem lpUniformEquiv_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : ∀ i, E i ≃L[𝕜] F i) {C D : ℝ}
    (hC : 0 ≤ C) (he : ∀ i, ‖(e i).toContinuousLinearMap‖ ≤ C)
    (hD : 0 ≤ D) (hei : ∀ i, ‖(e i).symm.toContinuousLinearMap‖ ≤ D)
    (x : lp E p) (i : ι) : lpUniformEquiv p e hC he hD hei x i = e i (x i) := rfl

@[simp] theorem lpUniformEquiv_symm_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : ∀ i, E i ≃L[𝕜] F i) {C D : ℝ}
    (hC : 0 ≤ C) (he : ∀ i, ‖(e i).toContinuousLinearMap‖ ≤ C)
    (hD : 0 ≤ D) (hei : ∀ i, ‖(e i).symm.toContinuousLinearMap‖ ≤ D)
    (x : lp F p) (i : ι) : (lpUniformEquiv p e hC he hD hei).symm x i =
      (e i).symm (x i) := rfl

theorem lpUniformEquiv_norm_le (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : ∀ i, E i ≃L[𝕜] F i) {C D : ℝ}
    (hC : 0 ≤ C) (he : ∀ i, ‖(e i).toContinuousLinearMap‖ ≤ C)
    (hD : 0 ≤ D) (hei : ∀ i, ‖(e i).symm.toContinuousLinearMap‖ ≤ D) :
    ‖(lpUniformEquiv p e hC he hD hei).toContinuousLinearMap‖ ≤ C :=
  lp.norm_mapCLM_le p (fun i => (e i).toContinuousLinearMap) hC he

theorem lpUniformEquiv_symm_norm_le (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : ∀ i, E i ≃L[𝕜] F i) {C D : ℝ}
    (hC : 0 ≤ C) (he : ∀ i, ‖(e i).toContinuousLinearMap‖ ≤ C)
    (hD : 0 ≤ D) (hei : ∀ i, ‖(e i).symm.toContinuousLinearMap‖ ≤ D) :
    ‖(lpUniformEquiv p e hC he hD hei).symm.toContinuousLinearMap‖ ≤ D :=
  lp.norm_mapCLM_le p (fun i => (e i).symm.toContinuousLinearMap) hD hei

theorem lpUniformEquiv_norm_bounds (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : ∀ i, E i ≃L[𝕜] F i) {C D : ℝ}
    (hC : 0 ≤ C) (he : ∀ i, ‖(e i).toContinuousLinearMap‖ ≤ C)
    (hD : 0 ≤ D) (hei : ∀ i, ‖(e i).symm.toContinuousLinearMap‖ ≤ D)
    (x : lp E p) :
    ‖lpUniformEquiv p e hC he hD hei x‖ ≤ C * ‖x‖ ∧
      ‖x‖ ≤ D * ‖lpUniformEquiv p e hC he hD hei x‖ := by
  let f := lpUniformEquiv p e hC he hD hei
  constructor
  · exact f.toContinuousLinearMap.le_of_opNorm_le
      (lpUniformEquiv_norm_le p e hC he hD hei) x
  · have h := f.symm.toContinuousLinearMap.le_of_opNorm_le
      (lpUniformEquiv_symm_norm_le p e hC he hD hei) (f x)
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using h

end ComplementedSubspace
