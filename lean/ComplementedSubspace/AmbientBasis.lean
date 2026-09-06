import ComplementedSubspace.AmbientLattice
import ComplementedSubspace.DenseContractions
import Mathlib.Analysis.Normed.Module.Bases

/-!
# Scalar coordinates of the actual ambient sum

The scalar coordinate family is indexed by the countable union of the finite
block indices. Its multiplier estimates use the inherited norm on the sum.
-/

noncomputable section
open scoped BigOperators ENNReal

namespace ComplementedSubspace

abbrev AmbientScalarIndex (a : BlockParameters) := Σ j, Fin (a.dimension j)

def ambientScalarVector (a : BlockParameters) (s : AmbientScalarIndex a) : Ambient a :=
  blockInclusion a s.1 (PiLp.single (ENNReal.ofReal (a.exponent s.1)) s.2 1)

def ambientScalarCoordinate (a : BlockParameters) (s : AmbientScalarIndex a) :
    Ambient a →L[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) (ENNReal.ofReal (a.exponent s.1))
    (fun _ : Fin (a.dimension s.1) => ℝ) s.2).comp (blockEvaluation a s.1)

@[simp] theorem ambientScalarCoordinate_apply (a : BlockParameters)
    (s : AmbientScalarIndex a) (x : Ambient a) :
    ambientScalarCoordinate a s x = x s.1 s.2 := rfl

theorem ambientScalarVector_norm (a : BlockParameters) (s : AmbientScalarIndex a) :
    ‖ambientScalarVector a s‖ = 1 := by
  rw [ambientScalarVector, norm_blockInclusion, PiLp.norm_single]
  norm_num

theorem ambientScalarCoordinate_vector (a : BlockParameters)
    (s t : AmbientScalarIndex a) :
    ambientScalarCoordinate a s (ambientScalarVector a t) = if s = t then 1 else 0 := by
  classical
  rcases s with ⟨j, i⟩
  rcases t with ⟨k, l⟩
  by_cases h : j = k
  · subst k
    simp [ambientScalarCoordinate_apply, ambientScalarVector, blockInclusion,
      PiLp.single_apply]
  · simp [ambientScalarCoordinate_apply, ambientScalarVector, blockInclusion,
      lp.single_apply, h]

/-- A finitely supported scalar coordinate multiplier on the ambient space. -/
def ambientScalarMultiplier (a : BlockParameters)
    (s : Finset (AmbientScalarIndex a)) (θ : AmbientScalarIndex a → ℝ) :
    Ambient a →L[ℝ] Ambient a :=
  ∑ i ∈ s, (ambientScalarCoordinate a i).smulRight (θ i • ambientScalarVector a i)

theorem ambientScalarCoordinate_multiplier (a : BlockParameters)
    (s : Finset (AmbientScalarIndex a)) (θ : AmbientScalarIndex a → ℝ)
    (x : Ambient a) (i : AmbientScalarIndex a) :
    ambientScalarCoordinate a i (ambientScalarMultiplier a s θ x) =
      if i ∈ s then θ i * ambientScalarCoordinate a i x else 0 := by
  classical
  simp only [ambientScalarMultiplier, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, map_sum, map_smul,
    ambientScalarCoordinate_vector, smul_eq_mul]
  simp [mul_comm, eq_comm]

theorem ambientScalarMultiplier_norm_le (a : BlockParameters)
    (s : Finset (AmbientScalarIndex a)) (θ : AmbientScalarIndex a → ℝ)
    (hθ : ∀ i, ‖θ i‖ ≤ 1) (x : Ambient a) :
    ‖ambientScalarMultiplier a s θ x‖ ≤ ‖x‖ := by
  apply HasSolidNorm.solid
  intro j i
  change |ambientScalarCoordinate a ⟨j, i⟩ (ambientScalarMultiplier a s θ x)| ≤
    |ambientScalarCoordinate a ⟨j, i⟩ x|
  rw [ambientScalarCoordinate_multiplier]
  split_ifs
  · rw [abs_mul]
    have h := hθ ⟨j, i⟩
    rw [Real.norm_eq_abs] at h
    exact (mul_le_mul_of_nonneg_right h (abs_nonneg _)).trans (by simp)
  · simp

theorem ambientScalarVector_linearIndependent (a : BlockParameters) :
    LinearIndependent ℝ (ambientScalarVector a) := by
  classical
  refine linearIndependent_iff.mpr fun l hl => l.ext ?_
  simpa [-ambientScalarCoordinate_apply, l.linearCombination_apply, Finsupp.sum,
    ambientScalarCoordinate_vector]
    using fun i => congrArg (ambientScalarCoordinate a i) hl

theorem blockInclusion_mem_scalar_span (a : BlockParameters) (j : ℕ) (x : Block a j) :
    blockInclusion a j x ∈ Submodule.span ℝ (Set.range (ambientScalarVector a)) := by
  classical
  have hx : x = ∑ i : Fin (a.dimension j),
      x i • PiLp.single (ENNReal.ofReal (a.exponent j)) i (1 : ℝ) := by
    ext k
    simp [PiLp.smul_apply, PiLp.single_apply, Pi.single_apply]
  rw [hx, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨j, i⟩, rfl⟩

theorem ambientScalarVector_dense_span (a : BlockParameters) :
    Dense (Submodule.span ℝ (Set.range (ambientScalarVector a)) : Set (Ambient a)) := by
  let W := Submodule.span ℝ (Set.range (ambientScalarVector a))
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  intro x _
  apply W.isClosed_topologicalClosure.mem_of_tendsto (hasSum_blockProjection a x)
  apply Filter.Eventually.of_forall
  intro s
  apply W.topologicalClosure.sum_mem
  intro j _
  apply W.le_topologicalClosure
  exact blockInclusion_mem_scalar_span a j (blockEvaluation a j x)

theorem ambientScalarMultiplier_one_vector (a : BlockParameters)
    (s : Finset (AmbientScalarIndex a)) (i : AmbientScalarIndex a) :
    ambientScalarMultiplier a s (fun _ => 1) (ambientScalarVector a i) =
      if i ∈ s then ambientScalarVector a i else 0 := by
  classical
  simp only [ambientScalarMultiplier, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ambientScalarCoordinate_vector,
    one_smul]
  simp [eq_comm]

theorem ambientScalarMultiplier_eventually_eq (a : BlockParameters)
    {y : Ambient a}
    (hy : y ∈ Submodule.span ℝ (Set.range (ambientScalarVector a))) :
    ∀ᶠ s in Filter.atTop, ambientScalarMultiplier a s (fun _ => 1) y = y := by
  classical
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    filter_upwards [Filter.eventually_ge_atTop ({i} : Finset (AmbientScalarIndex a))]
      with s hs
    rw [ambientScalarMultiplier_one_vector, if_pos (hs (by simp))]
  | zero => exact Filter.Eventually.of_forall fun _ => map_zero _
  | add x y hx hy ihx ihy =>
    filter_upwards [ihx, ihy] with s hsx hsy
    rw [map_add, hsx, hsy]
  | smul c x hx ih =>
    filter_upwards [ih] with s hs
    rw [map_smul, hs]

/-- Norm convergence over all finite scalar subsets, not just whole blocks. -/
theorem hasSum_ambientScalarVector (a : BlockParameters) (x : Ambient a) :
    HasSum (fun i => ambientScalarCoordinate a i x • ambientScalarVector a i) x := by
  classical
  have h := tendsto_contractions_of_dense Filter.atTop
    (fun s => ambientScalarMultiplier a s (fun _ => 1))
    (fun s y => ambientScalarMultiplier_norm_le a s (fun _ => 1) (by simp) y)
    (ambientScalarVector_dense_span a)
    (fun y hy => ambientScalarMultiplier_eventually_eq a hy) x
  change Filter.Tendsto (fun s : Finset (AmbientScalarIndex a) =>
    ∑ i ∈ s, ambientScalarCoordinate a i x • ambientScalarVector a i)
      Filter.atTop (nhds x)
  simpa only [ambientScalarMultiplier, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, one_smul] using h

/-- The actual unconditional scalar Schauder basis, initially with its
natural dependent coordinate index. -/
def ambientScalarSchauderBasis (a : BlockParameters) :
    UnconditionalSchauderBasis (AmbientScalarIndex a) ℝ (Ambient a) where
  basis := ambientScalarVector a
  coord := ambientScalarCoordinate a
  ortho := by
    classical
    intro i j
    rw [ambientScalarCoordinate_vector]
    by_cases hij : i = j <;> simp [Pi.single_apply, hij, eq_comm]
  expansion := hasSum_ambientScalarVector a

end ComplementedSubspace
