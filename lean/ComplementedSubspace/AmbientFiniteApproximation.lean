import ComplementedSubspace.AmbientBasis
import ComplementedSubspace.LatticeApproximation

/-!
# Sharp local unconditional bounds for the ambient space and its dual

The primal argument uses density of finite scalar coordinate spans. The dual
argument reuses the proved order-complete lattice approximation theorem; it
does not identify the dual of an infinite sum explicitly.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators ENNReal NNReal

namespace ComplementedSubspace

section DenseDisjoint

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E] {ι : Type*}

/-- Density of the span of a disjoint family supplies simultaneous finite
1-unconditional approximation in the inherited lattice norm. -/
theorem hasFiniteUnconditionalApproximations_of_dense_disjoint_span
    (v : ι → E) (hdis : Pairwise fun i j => IsVLDisjoint (v i) (v j))
    (hdense : Dense (Submodule.span ℝ (Set.range v) : Set E)) :
    HasFiniteUnconditionalApproximations E 1 := by
  classical
  intro m x δ hδ
  let y : Fin m → E := fun i => (hdense.exists_dist_lt (x i) hδ).choose
  have hy (i : Fin m) : y i ∈ Submodule.span ℝ (Set.range v) ∧
      dist (x i) (y i) < δ := (hdense.exists_dist_lt (x i) hδ).choose_spec
  let t : Finset E := Finset.univ.image y
  have ht : (t : Set E) ⊆ Submodule.span ℝ (Set.range v) := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact (hy i).1
  obtain ⟨T, hT, htT⟩ := Submodule.subset_span_finite_of_subset_span ht
  let w : T → E := fun z => z.val
  have hw : Pairwise fun i j => IsVLDisjoint (w i) (w j) := by
    intro i j hij
    obtain ⟨a, ha⟩ := hT i.property
    obtain ⟨b, hb⟩ := hT j.property
    change IsVLDisjoint i.val j.val
    rw [← ha, ← hb]
    apply hdis
    intro hab
    apply hij
    apply Subtype.ext
    exact ha.symm.trans (hab ▸ hb)
  obtain ⟨n, b, hb⟩ := exists_unconditional_basis_of_disjoint w hw
  let F := Submodule.span ℝ (Set.range w)
  have hTF : Submodule.span ℝ (T : Set E) ≤ F :=
    Submodule.span_mono (fun z hz => ⟨⟨z, hz⟩, rfl⟩)
  refine ⟨F, n, b, by simpa using hb, ?_⟩
  intro i
  have hyt : y i ∈ t := Finset.mem_image_of_mem y (Finset.mem_univ i)
  refine ⟨⟨y i, hTF (htT hyt)⟩, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using (hy i).2.le

end DenseDisjoint

theorem ambientScalarVector_pairwise_disjoint (a : BlockParameters) :
    Pairwise fun s t => IsVLDisjoint (ambientScalarVector a s) (ambientScalarVector a t) := by
  intro s t hst
  change |ambientScalarVector a s| ⊓ |ambientScalarVector a t| = 0
  ext j i
  change |ambientScalarCoordinate a ⟨j, i⟩ (ambientScalarVector a s)| ⊓
    |ambientScalarCoordinate a ⟨j, i⟩ (ambientScalarVector a t)| = 0
  rw [ambientScalarCoordinate_vector, ambientScalarCoordinate_vector]
  by_cases hs : (⟨j, i⟩ : AmbientScalarIndex a) = s
  · have ht : (⟨j, i⟩ : AmbientScalarIndex a) ≠ t := by
      intro ht
      exact hst (hs.symm.trans ht)
    simp [hs, hst]
  · simp [hs]

theorem ambient_hasFiniteUnconditionalApproximations (a : BlockParameters) :
    HasFiniteUnconditionalApproximations (Ambient a) 1 := by
  letI : VectorLattice (Ambient a) := {}
  letI : NormedVectorLattice (Ambient a) := {}
  exact hasFiniteUnconditionalApproximations_of_dense_disjoint_span
    (ambientScalarVector a) (ambientScalarVector_pairwise_disjoint a)
    (ambientScalarVector_dense_span a)

theorem ambient_chiDPR_le_one (a : BlockParameters) : chiDPR (Ambient a) ≤ 1 :=
  chiDPR_le_constant_of_finite_approximations 1 le_rfl
    (ambient_hasFiniteUnconditionalApproximations a)

theorem ambient_chiGL_le_one (a : BlockParameters) : chiGL (Ambient a) ≤ 1 :=
  (chiGL_le_chiDPR (Ambient a)).trans (ambient_chiDPR_le_one a)

/-- The ambient dual is an order-complete Banach lattice in its actual
operator norm. Reusing that theorem avoids a countable-sum duality development. -/
theorem ambientDual_hasFiniteUnconditionalApproximations (a : BlockParameters) :
    HasFiniteUnconditionalApproximations (StrongDual ℝ (Ambient a)) 1 := by
  letI : VectorLattice (Ambient a) := {}
  letI : NormedVectorLattice (Ambient a) := {}
  letI : BanachLattice (Ambient a) := {}
  exact hasFiniteUnconditionalApproximations_dual

theorem ambientDual_chiDPR_le_one (a : BlockParameters) :
    chiDPR (StrongDual ℝ (Ambient a)) ≤ 1 := by
  letI : VectorLattice (Ambient a) := {}
  letI : NormedVectorLattice (Ambient a) := {}
  letI : BanachLattice (Ambient a) := {}
  exact chiDPR_dual_lattice_le_one

theorem ambientDual_chiGL_le_one (a : BlockParameters) :
    chiGL (StrongDual ℝ (Ambient a)) ≤ 1 :=
  (chiGL_le_chiDPR (StrongDual ℝ (Ambient a))).trans (ambientDual_chiDPR_le_one a)

end ComplementedSubspace

