import ComplementedSubspace.FiniteHeadHilbert
import ComplementedSubspace.RecursiveParameters

/-! The recursively chosen full-block bounds give actual Hilbert norms on
every finite inherited profile head, including complementary projection ranges. -/
noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

/-- The finite head embeds linearly in the finite product of its coordinates. -/
instance finiteDimensional_finite_lp_two {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)] : FiniteDimensional ℝ (lp E 2) := by
  let A : lp E 2 →ₗ[ℝ] (∀ i, E i) :=
    { toFun := fun x i => x i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective A
  intro x y h
  ext i
  exact congrFun h i

theorem block_hasHilbertNormWithin (a : BlockParameters) (i : ℕ) :
    HasHilbertNormWithin (Block a i)
      (((a.dimension i : ℕ) : ℝ) ^ (1 / 2 - 1 / a.exponent i)) := by
  letI : NeZero (a.dimension i : ℕ) := ⟨(a.dimension i).pos.ne'⟩
  simpa only [Fintype.card_fin] using
    (finitePiLp_hasHilbertNormWithin (ι := Fin (a.dimension i)) (a.two_lt_exponent i).le)

theorem blockProfile_finiteHead_hasHilbertNormWithin (a : BlockParameters)
    (S : ∀ i : ℕ, Submodule ℝ (Block a i)) (j : ℕ)
    {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ i < j, (((a.dimension i : ℕ) : ℝ) ^ (1 / 2 - 1 / a.exponent i)) ≤ D) :
    HasHilbertNormWithin (lp (fun i : Fin j => S i.val) 2) D := by
  apply hasHilbertNormWithin_finite_lp_two hD
  intro i
  exact ((block_hasHilbertNormWithin a i.val).subspace (S i.val)).mono (hbound i.val i.isLt)

theorem recursiveProfile_finiteHead_hasHilbertNormWithin {η : ℝ} {θ : ℕ → ℝ}
    (s : RecursiveFrameSelection η θ)
    (S : ∀ i : ℕ, Submodule ℝ (Block s.toBlockParameters i)) (j : ℕ) :
    HasHilbertNormWithin (lp (fun i : Fin j => S i.val) 2) (s.headBound j) := by
  apply blockProfile_finiteHead_hasHilbertNormWithin s.toBlockParameters S j
    (by have h := s.headBound_ge_index j; nlinarith [Nat.cast_nonneg (α := ℝ) j])
  intro i hij
  have h := s.earlier_ambient_bound i j hij
  change ((4 : ℝ) ^ (s.block i).order) ^ (1 / 2 - 1 / (s.block i).exponent) ≤ s.headBound j at h
  simpa only [RecursiveFrameSelection.toBlockParameters_dimension,
    RecursiveFrameSelection.toBlockParameters_exponent, Nat.cast_pow, Nat.cast_ofNat] using h

theorem recursiveProfile_finiteHead_dual_hasHilbertNormWithin {η : ℝ} {θ : ℕ → ℝ}
    (s : RecursiveFrameSelection η θ)
    (S : ∀ i : ℕ, Submodule ℝ (Block s.toBlockParameters i)) (j : ℕ) :
    HasHilbertNormWithin (StrongDual ℝ (lp (fun i : Fin j => S i.val) 2)) (s.headBound j) := by
  apply (recursiveProfile_finiteHead_hasHilbertNormWithin s S j).dual
  have h := s.headBound_ge_index j
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

/-- The concrete model and its inherited-norm comparison, ready for the
head-tail local Hilbert combination theorem. -/
theorem recursiveProfile_finiteHead_hilbertModel {η : ℝ} {θ : ℕ → ℝ}
    (s : RecursiveFrameSelection η θ)
    (S : ∀ i : ℕ, Submodule ℝ (Block s.toBlockParameters i)) (j : ℕ) :
    ∃ q : HilbertNormModel (lp (fun i : Fin j => S i.val) 2),
      ∀ x, q.q x ≤ ‖x‖ ∧ ‖x‖ ≤ s.headBound j * q.q x :=
  (recursiveProfile_finiteHead_hasHilbertNormWithin s S j).exists_model

end ComplementedSubspace
