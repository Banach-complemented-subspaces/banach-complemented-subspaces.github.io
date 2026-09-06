import ComplementedSubspace.ComplexAmbient
import ComplementedSubspace.DenseContractionsScalar
import ComplementedSubspace.CorollaryStatement
import Mathlib.Analysis.Normed.Module.Bases
import Mathlib.Basic.Denumerable

/-! A genuine sequential one-unconditional Schauder basis for the complex
ambient sum, with the full complex scalar multiplier condition. -/
noncomputable section
open scoped BigOperators ENNReal
namespace ComplementedSubspace
abbrev ComplexAmbientScalarIndex (a : BlockParameters) := Σ j, Fin (a.dimension j)

def complexAmbientScalarVector (a : BlockParameters) (s : ComplexAmbientScalarIndex a) : ComplexAmbient a :=
  complexBlockInclusion a s.1 (PiLp.single (ENNReal.ofReal (a.exponent s.1)) s.2 1)

def complexAmbientScalarCoordinate (a : BlockParameters) (s : ComplexAmbientScalarIndex a) :
    ComplexAmbient a →L[ℂ] ℂ :=
  (PiLp.proj (𝕜 := ℂ) (ENNReal.ofReal (a.exponent s.1))
    (fun _ : Fin (a.dimension s.1) => ℂ) s.2).comp (complexBlockEvaluation a s.1)

@[simp] theorem complexAmbientScalarCoordinate_apply (a : BlockParameters)
    (s : ComplexAmbientScalarIndex a) (x : ComplexAmbient a) :
    complexAmbientScalarCoordinate a s x = x s.1 s.2 := rfl

theorem complexAmbientScalarVector_norm (a : BlockParameters) (s : ComplexAmbientScalarIndex a) :
    ‖complexAmbientScalarVector a s‖ = 1 := by
  rw [complexAmbientScalarVector, norm_complexBlockInclusion, PiLp.norm_single]
  norm_num

theorem complexAmbientScalarCoordinate_vector (a : BlockParameters)
    (s t : ComplexAmbientScalarIndex a) :
    complexAmbientScalarCoordinate a s (complexAmbientScalarVector a t) = if s = t then 1 else 0 := by
  classical
  rcases s with ⟨j, i⟩
  rcases t with ⟨k, l⟩
  by_cases h : j = k
  · subst k
    simp [complexAmbientScalarCoordinate_apply, complexAmbientScalarVector, complexBlockInclusion,
      PiLp.single_apply]
  · simp [complexAmbientScalarCoordinate_apply, complexAmbientScalarVector, complexBlockInclusion,
      lp.single_apply, h]

/-- A finitely supported scalar coordinate multiplier on the complexAmbient space. -/
def complexAmbientScalarMultiplier (a : BlockParameters)
    (s : Finset (ComplexAmbientScalarIndex a)) (θ : ComplexAmbientScalarIndex a → ℂ) :
    ComplexAmbient a →L[ℂ] ComplexAmbient a :=
  ∑ i ∈ s, (complexAmbientScalarCoordinate a i).smulRight (θ i • complexAmbientScalarVector a i)

theorem complexAmbientScalarCoordinate_multiplier (a : BlockParameters)
    (s : Finset (ComplexAmbientScalarIndex a)) (θ : ComplexAmbientScalarIndex a → ℂ)
    (x : ComplexAmbient a) (i : ComplexAmbientScalarIndex a) :
    complexAmbientScalarCoordinate a i (complexAmbientScalarMultiplier a s θ x) =
      if i ∈ s then θ i * complexAmbientScalarCoordinate a i x else 0 := by
  classical
  simp only [complexAmbientScalarMultiplier, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, map_sum, map_smul,
    complexAmbientScalarCoordinate_vector, smul_eq_mul]
  simp [mul_comm, eq_comm]

theorem complexBlock_norm_mono (a : BlockParameters) (j : ℕ)
    (x y : ComplexBlock a j) (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  have hp : 0 < (ENNReal.ofReal (a.exponent j)).toReal := by
    rw [ENNReal.toReal_ofReal (by linarith [a.two_lt_exponent j])]
    linarith [a.two_lt_exponent j]
  rw [PiLp.norm_eq_sum hp, PiLp.norm_eq_sum hp]
  apply Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg (x i)) _) _
    (one_div_nonneg.mpr hp.le)
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg (x i)) (h i) hp.le

/-- Every finite complex multiplier with modulus at most one is contractive,
including arbitrary complex phases. -/
theorem complexAmbientScalarMultiplier_norm_le (a : BlockParameters)
    (s : Finset (ComplexAmbientScalarIndex a)) (θ : ComplexAmbientScalarIndex a → ℂ)
    (hθ : ∀ i, ‖θ i‖ ≤ 1) (x : ComplexAmbient a) :
    ‖complexAmbientScalarMultiplier a s θ x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro j
  apply complexBlock_norm_mono
  intro i
  change ‖complexAmbientScalarCoordinate a ⟨j, i⟩ (complexAmbientScalarMultiplier a s θ x)‖ ≤
    ‖complexAmbientScalarCoordinate a ⟨j, i⟩ x‖
  rw [complexAmbientScalarCoordinate_multiplier]
  split_ifs
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hθ ⟨j, i⟩) (norm_nonneg _)).trans_eq (one_mul _)
  · simp
theorem complexAmbientScalarVector_linearIndependent (a : BlockParameters) :
    LinearIndependent ℂ (complexAmbientScalarVector a) := by
  classical
  refine linearIndependent_iff.mpr fun l hl => l.ext ?_
  simpa [-complexAmbientScalarCoordinate_apply, l.linearCombination_apply, Finsupp.sum,
    complexAmbientScalarCoordinate_vector]
    using fun i => congrArg (complexAmbientScalarCoordinate a i) hl

theorem complexBlockInclusion_mem_scalar_span (a : BlockParameters) (j : ℕ) (x : ComplexBlock a j) :
    complexBlockInclusion a j x ∈ Submodule.span ℂ (Set.range (complexAmbientScalarVector a)) := by
  classical
  have hx : x = ∑ i : Fin (a.dimension j),
      x i • PiLp.single (ENNReal.ofReal (a.exponent j)) i (1 : ℂ) := by
    ext k
    simp [PiLp.smul_apply, PiLp.single_apply, Pi.single_apply]
  rw [hx, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨j, i⟩, rfl⟩

theorem complexAmbientScalarVector_dense_span (a : BlockParameters) :
    Dense (Submodule.span ℂ (Set.range (complexAmbientScalarVector a)) : Set (ComplexAmbient a)) := by
  let W := Submodule.span ℂ (Set.range (complexAmbientScalarVector a))
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  intro x _
  apply W.isClosed_topologicalClosure.mem_of_tendsto (hasSum_complexBlockProjection a x)
  apply Filter.Eventually.of_forall
  intro s
  apply W.topologicalClosure.sum_mem
  intro j _
  apply W.le_topologicalClosure
  exact complexBlockInclusion_mem_scalar_span a j (complexBlockEvaluation a j x)

theorem complexAmbientScalarMultiplier_one_vector (a : BlockParameters)
    (s : Finset (ComplexAmbientScalarIndex a)) (i : ComplexAmbientScalarIndex a) :
    complexAmbientScalarMultiplier a s (fun _ => 1) (complexAmbientScalarVector a i) =
      if i ∈ s then complexAmbientScalarVector a i else 0 := by
  classical
  simp only [complexAmbientScalarMultiplier, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, complexAmbientScalarCoordinate_vector,
    one_smul]
  simp [eq_comm]

theorem complexAmbientScalarMultiplier_eventually_eq (a : BlockParameters)
    {y : ComplexAmbient a}
    (hy : y ∈ Submodule.span ℂ (Set.range (complexAmbientScalarVector a))) :
    ∀ᶠ s in Filter.atTop, complexAmbientScalarMultiplier a s (fun _ => 1) y = y := by
  classical
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    filter_upwards [Filter.eventually_ge_atTop ({i} : Finset (ComplexAmbientScalarIndex a))]
      with s hs
    rw [complexAmbientScalarMultiplier_one_vector, if_pos (hs (by simp))]
  | zero => exact Filter.Eventually.of_forall fun _ => map_zero _
  | add x y hx hy ihx ihy =>
    filter_upwards [ihx, ihy] with s hsx hsy
    rw [map_add, hsx, hsy]
  | smul c x hx ih =>
    filter_upwards [ih] with s hs
    rw [map_smul, hs]

/-- Norm convergence over all finite scalar subsets, not just whole complexBlocks. -/
theorem hasSum_complexAmbientScalarVector (a : BlockParameters) (x : ComplexAmbient a) :
    HasSum (fun i => complexAmbientScalarCoordinate a i x • complexAmbientScalarVector a i) x := by
  classical
  have h := tendsto_contractions_of_dense_over Filter.atTop
    (fun s => complexAmbientScalarMultiplier a s (fun _ => 1))
    (fun s y => complexAmbientScalarMultiplier_norm_le a s (fun _ => 1) (by simp) y)
    (complexAmbientScalarVector_dense_span a)
    (fun y hy => complexAmbientScalarMultiplier_eventually_eq a hy) x
  change Filter.Tendsto (fun s : Finset (ComplexAmbientScalarIndex a) =>
    ∑ i ∈ s, complexAmbientScalarCoordinate a i x • complexAmbientScalarVector a i)
      Filter.atTop (nhds x)
  simpa only [complexAmbientScalarMultiplier, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, one_smul] using h

/-- The actual unconditional scalar Schauder basis, initially with its
natural dependent coordinate index. -/
def complexAmbientScalarSchauderBasis (a : BlockParameters) :
    UnconditionalSchauderBasis (ComplexAmbientScalarIndex a) ℂ (ComplexAmbient a) where
  basis := complexAmbientScalarVector a
  coord := complexAmbientScalarCoordinate a
  ortho := by
    classical
    intro i j
    rw [complexAmbientScalarCoordinate_vector]
    by_cases hij : i = j <;> simp [Pi.single_apply, hij, eq_comm]
  expansion := hasSum_complexAmbientScalarVector a


instance complexAmbientScalarIndex_infinite (a : BlockParameters) :
    Infinite (ComplexAmbientScalarIndex a) :=
  Infinite.of_injective (fun j : ℕ => (⟨j, ⟨0, (a.dimension j).pos⟩⟩ :
    ComplexAmbientScalarIndex a)) (fun _ _ h => congrArg Sigma.fst h)

/-- Reindex the countable union of nonempty finite complexBlocks by the naturals. -/
def complexAmbientScalarEnumeration (a : BlockParameters) : ℕ ≃ ComplexAmbientScalarIndex a :=
  Classical.choice inferInstance

def complexAmbientSchauderBasis (a : BlockParameters) :
    UnconditionalSchauderBasis ℕ ℂ (ComplexAmbient a) where
  basis := fun i => complexAmbientScalarVector a (complexAmbientScalarEnumeration a i)
  coord := fun i => complexAmbientScalarCoordinate a (complexAmbientScalarEnumeration a i)
  ortho := by
    classical
    intro i j
    rw [complexAmbientScalarCoordinate_vector]
    simp [Pi.single_apply, eq_comm]
  expansion := fun x => (complexAmbientScalarEnumeration a).hasSum_iff.mpr
    (hasSum_complexAmbientScalarVector a x)

theorem complexAmbientSchauderBasis_one_unconditional (a : BlockParameters) :
    IsOneUnconditional (complexAmbientSchauderBasis a) := by
  classical
  intro s θ hθ x
  let e := complexAmbientScalarEnumeration a
  have heq : (∑ i ∈ s, (θ i * (complexAmbientSchauderBasis a).coord i x) •
      complexAmbientSchauderBasis a i) =
      complexAmbientScalarMultiplier a (s.map e.toEmbedding) (fun t => θ (e.symm t)) x := by
    simp only [complexAmbientScalarMultiplier, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply, Finset.sum_map, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply, smul_smul, complexAmbientSchauderBasis, e, mul_comm]
  rw [heq]
  exact complexAmbientScalarMultiplier_norm_le a _ _ (fun t => hθ (e.symm t)) x

theorem complexAmbient_hasOneUnconditionalSchauderBasis (a : BlockParameters) :
    HasOneUnconditionalSchauderBasis ℂ (ComplexAmbient a) :=
  ⟨complexAmbientSchauderBasis a, complexAmbientSchauderBasis_one_unconditional a⟩

end ComplementedSubspace

