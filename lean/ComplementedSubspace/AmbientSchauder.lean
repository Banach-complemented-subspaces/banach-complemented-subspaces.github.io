import ComplementedSubspace.AmbientBasis
import ComplementedSubspace.CorollaryStatement
import Mathlib.Basic.Denumerable

/-! # The actual sequential 1-unconditional basis of the real ambient space -/

noncomputable section
open scoped BigOperators

namespace ComplementedSubspace

instance ambientScalarIndex_infinite (a : BlockParameters) :
    Infinite (AmbientScalarIndex a) :=
  Infinite.of_injective (fun j : ℕ => (⟨j, ⟨0, (a.dimension j).pos⟩⟩ :
    AmbientScalarIndex a)) (fun _ _ h => congrArg Sigma.fst h)

/-- Reindex the countable union of nonempty finite blocks by the naturals. -/
def ambientScalarEnumeration (a : BlockParameters) : ℕ ≃ AmbientScalarIndex a :=
  Classical.choice inferInstance

def ambientSchauderBasis (a : BlockParameters) :
    UnconditionalSchauderBasis ℕ ℝ (Ambient a) where
  basis := fun i => ambientScalarVector a (ambientScalarEnumeration a i)
  coord := fun i => ambientScalarCoordinate a (ambientScalarEnumeration a i)
  ortho := by
    classical
    intro i j
    rw [ambientScalarCoordinate_vector]
    simp [Pi.single_apply, eq_comm]
  expansion := fun x => (ambientScalarEnumeration a).hasSum_iff.mpr
    (hasSum_ambientScalarVector a x)

theorem ambientSchauderBasis_one_unconditional (a : BlockParameters) :
    IsOneUnconditional (ambientSchauderBasis a) := by
  classical
  intro s θ hθ x
  let e := ambientScalarEnumeration a
  have heq : (∑ i ∈ s, (θ i * (ambientSchauderBasis a).coord i x) •
      ambientSchauderBasis a i) =
      ambientScalarMultiplier a (s.map e.toEmbedding) (fun t => θ (e.symm t)) x := by
    simp only [ambientScalarMultiplier, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply, Finset.sum_map, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply, smul_smul, ambientSchauderBasis, e, mul_comm]
  rw [heq]
  exact ambientScalarMultiplier_norm_le a _ _ (fun t => hθ (e.symm t)) x

theorem ambient_hasOneUnconditionalSchauderBasis (a : BlockParameters) :
    HasOneUnconditionalSchauderBasis ℝ (Ambient a) :=
  ⟨ambientSchauderBasis a, ambientSchauderBasis_one_unconditional a⟩

end ComplementedSubspace
