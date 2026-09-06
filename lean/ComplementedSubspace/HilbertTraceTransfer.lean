import ComplementedSubspace.LocalHilbertFactorization
import Mathlib.LinearAlgebra.Trace

/-! # Applying a Hilbert trace bound to a locally Hilbertian factorization -/

noncomputable section
namespace ComplementedSubspace

variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The trace hypothesis is explicit and is to be supplied by the concrete
frame trace theorem. This lemma accounts for the local Hilbert distortion. -/
theorem trace_comp_le_of_localHilbert {q : ℕ} {D a : ℝ}
    (hD : 0 ≤ D) (ha : 0 ≤ a) (hE : Module.finrank ℝ E ≤ q)
    (hlocal : ∀ (S : Submodule ℝ W) [FiniteDimensional ℝ S], Module.finrank ℝ S ≤ q →
      HasHilbertNormWithin S D)
    (htrace : ∀ (S : Submodule ℝ W) [FiniteDimensional ℝ S]
      (p : HilbertNormModel S) (U : E →L[ℝ] p.Space) (V : p.Space →L[ℝ] E),
      |LinearMap.trace ℝ E (V.comp U).toLinearMap| ≤ a * ‖U‖ * ‖V‖)
    (A : E →L[ℝ] W) (B : W →L[ℝ] E) :
    |LinearMap.trace ℝ E (B.comp A).toLinearMap| ≤ a * D * ‖A‖ * ‖B‖ := by
  obtain ⟨p, U, V, hcomp, hprod⟩ :=
    exists_hilbertFactorization_norm_product hD hlocal hE A B
  have ht := htrace A.range p U V
  rw [hcomp] at ht
  calc
    |LinearMap.trace ℝ E (B.comp A).toLinearMap| ≤ a * (‖U‖ * ‖V‖) := by
      simpa only [mul_assoc] using ht
    _ ≤ a * (D * ‖A‖ * ‖B‖) := mul_le_mul_of_nonneg_left hprod ha
    _ = a * D * ‖A‖ * ‖B‖ := by ring

end ComplementedSubspace
