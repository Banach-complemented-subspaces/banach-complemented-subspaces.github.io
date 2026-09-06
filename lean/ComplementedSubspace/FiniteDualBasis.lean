import ComplementedSubspace.GLDualRetraction
import Mathlib.LinearAlgebra.Dual.Basis

/-! Finite unconditional bases pass to the actual normed continuous dual. -/
noncomputable section
open scoped ENNReal NNReal
namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Algebraic coordinate functionals with their actual continuous-dual norm. -/
def continuousDualBasis {m : ℕ} (b : Module.Basis (Fin m) ℝ E) :
    Module.Basis (Fin m) ℝ (StrongDual ℝ E) :=
  b.dualBasis.map LinearMap.toContinuousLinearMap

@[simp] theorem continuousDualBasis_apply {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (i : Fin m) (x : E) :
    continuousDualBasis b i x = b.dualBasis i x := rfl

/-- Dual coordinate multipliers are precisely the adjoints of the original
coordinate multipliers, with no additional distortion factor. -/
theorem continuousDualBasis_multiplier {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (θ : Fin m → ℝ) :
    basisMultiplier (continuousDualBasis b) θ = dualPullback (basisMultiplier b θ) := by
  apply ContinuousLinearMap.coe_injective
  apply (continuousDualBasis b).ext
  intro i
  change basisMultiplier (continuousDualBasis b) θ (continuousDualBasis b i) =
    dualPullback (basisMultiplier b θ) (continuousDualBasis b i)
  rw [basisMultiplier_apply_basis]
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro j
  change θ i * b.dualBasis i (b j) = b.dualBasis i (basisMultiplier b θ (b j))
  rw [basisMultiplier_apply_basis, map_smul, smul_eq_mul, Module.Basis.dualBasis_apply_self]
  by_cases h : j = i
  · simp [h]
  · simp [h]

theorem continuousDualBasis_constant_le {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) :
    unconditionalBasisConstant (continuousDualBasis b) ≤ unconditionalBasisConstant b := by
  unfold unconditionalBasisConstant
  apply max_le_max le_rfl
  apply iSup_mono
  intro θ
  apply iSup_mono
  intro hθ
  rw [continuousDualBasis_multiplier]
  exact enorm_dualPullback_le _

theorem exists_continuousDualBasis_constant_le {m : ℕ}
    (b : Module.Basis (Fin m) ℝ E) (K : ℝ≥0∞)
    (hb : unconditionalBasisConstant b ≤ K) :
    ∃ c : Module.Basis (Fin m) ℝ (StrongDual ℝ E), unconditionalBasisConstant c ≤ K :=
  ⟨continuousDualBasis b, (continuousDualBasis_constant_le b).trans hb⟩

end ComplementedSubspace
