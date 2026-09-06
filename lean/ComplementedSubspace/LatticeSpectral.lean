import BanLat.Substructures.Band.PPP

/-!
# Finite spectral approximation by band partitions

The order-complete lattice argument uses only the principal projection property.
It replaces representation-theoretic discretization by finite threshold cuts.
-/

noncomputable section

open scoped BigOperators

namespace ComplementedSubspace

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- The principal band of the positive part separates the positive and negative
parts of a vector. This is the elementary spectral threshold cut. -/
theorem exists_bandProjection_posPart [HasPrincipalProjectionProperty X] (v : X) :
    ∃ P : ProjectionBand X,
      P.bandProjection v = v⁺ ∧ Pᶜ.bandProjection v = -v⁻ := by
  obtain ⟨P, hP⟩ := HasPrincipalProjectionProperty.exists_projectionBand v⁺
  have hpos : v⁺ ∈ (P : Set X) := by
    rw [hP]
    exact Band.subset_generated _ rfl
  have hgen : (Band.generated ({v⁺} : Set X) : Set X) ⊆
      disjointComplement ({v⁻} : Set X) := by
    apply Band.generated_le (B := Band.disjointComplement ({v⁻} : Set X))
    rintro z rfl w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact isVLDisjoint_posPart_negPart v
  have hneg : v⁻ ∈ disjointComplement (P : Set X) := by
    intro z hz
    have hz' : z ∈ (Band.generated ({v⁺} : Set X) : Set X) := by
      simpa [hP] using hz
    exact isVLDisjoint_comm.mp (hgen hz' _ (Set.mem_singleton _))
  have hp : P.bandProjection v = v⁺ := by
    conv_lhs => rw [← posPart_sub_negPart v]
    rw [map_sub, P.bandProjection_eq_of_mem hpos,
      P.bandProjection_eq_zero_of_mem_dc hneg, sub_zero]
  refine ⟨P, hp, ?_⟩
  rw [ProjectionBand.bandProjection_compl]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, hp]
  calc
    v - v⁺ = (v⁺ - v⁻) - v⁺ := by rw [posPart_sub_negPart]
    _ = -v⁻ := by abel

/-- A finite spectral cut gives opposite order bounds on the two complementary
bands. No norm or representation of the lattice is involved. -/
theorem exists_bandProjection_threshold [HasPrincipalProjectionProperty X]
    (x u : X) (t : ℝ) :
    ∃ P : ProjectionBand X,
      t • P.bandProjection u ≤ P.bandProjection x ∧
      Pᶜ.bandProjection x ≤ t • Pᶜ.bandProjection u := by
  obtain ⟨P, hP, hPc⟩ := exists_bandProjection_posPart (x - t • u)
  refine ⟨P, ?_, ?_⟩
  · apply sub_nonneg.mp
    have h := posPart_nonneg (x - t • u)
    rw [← hP] at h
    simpa only [map_sub, map_smul] using h
  · apply sub_nonpos.mp
    have h := neg_nonpos.mpr (negPart_nonneg (x - t • u))
    rw [← hPc] at h
    simpa only [map_sub, map_smul] using h

/-- Finite pairwise disjoint projection bands whose projections sum to the
identity. Empty and zero cells are allowed. -/
structure LatticeBandPartition (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] where
  Index : Type
  [finite : Fintype Index]
  band : Index → ProjectionBand X
  disjoint : Pairwise fun i j => band i ≤ (band j)ᶜ
  total : ∑ i, (band i).bandProjection = LinearMap.id

attribute [instance] LatticeBandPartition.finite

namespace LatticeBandPartition

def trivial : LatticeBandPartition X where
  Index := Unit
  finite := inferInstance
  band := fun _ => ⊤
  disjoint := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  total := by
    simp only [Fintype.sum_unique]
    ext x
    exact ProjectionBand.bandProjection_eq_of_mem _ (by trivial)

theorem sum_apply (P : LatticeBandPartition X) (x : X) :
    ∑ i, (P.band i).bandProjection x = x := by
  have h := congrArg (fun T : X →ₗ[ℝ] X => T x) P.total
  simpa using h

theorem positive (P : LatticeBandPartition X) {u : X} (hu : 0 ≤ u) (i : P.Index) :
    0 ≤ (P.band i).bandProjection u :=
  Positive.zero_le_iff.mp (P.band i).bandProjection_nonneg u hu

theorem pairwise_disjoint (P : LatticeBandPartition X) (u : X) :
    Pairwise fun i j => IsVLDisjoint ((P.band i).bandProjection u)
      ((P.band j).bandProjection u) := by
  intro i j hij
  have hmem := P.disjoint hij ((P.band i).bandProjection_mem u)
  exact hmem _ ((P.band j).bandProjection_mem u)

/-- Common refinement of two finite band partitions. -/
def common (P Q : LatticeBandPartition X) : LatticeBandPartition X where
  Index := P.Index × Q.Index
  finite := inferInstance
  band := fun ij => P.band ij.1 ⊓ Q.band ij.2
  disjoint := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hne
    apply le_compl_iff_disjoint_right.mpr
    by_cases hik : i = k
    · have hjl : j ≠ l := by
        intro h; exact hne (Prod.ext hik h)
      exact (le_compl_iff_disjoint_right.mp (Q.disjoint hjl)).mono
        inf_le_right inf_le_right
    · exact (le_compl_iff_disjoint_right.mp (P.disjoint hik)).mono
        inf_le_left inf_le_left
  total := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.id_apply, Fintype.sum_prod_type,
      ProjectionBand.bandProjection_inf, LinearMap.comp_apply]
    simp_rw [← map_sum, Q.sum_apply]
    exact P.sum_apply x

/-- Splitting every cell by a possibly different cut keeps a finite partition. -/
def split (P : LatticeBandPartition X) (cut : P.Index → ProjectionBand X) :
    LatticeBandPartition X where
  Index := P.Index × Bool
  finite := inferInstance
  band := fun ib => P.band ib.1 ⊓ if ib.2 then cut ib.1 else (cut ib.1)ᶜ
  disjoint := by
    rintro ⟨i, b⟩ ⟨j, c⟩ hne
    apply le_compl_iff_disjoint_right.mpr
    by_cases hij : i = j
    · subst j
      have hbc : b ≠ c := by intro h; exact hne (Prod.ext rfl h)
      cases b <;> cases c
      · exact (hbc rfl).elim
      · exact (disjoint_compl_left).mono inf_le_right inf_le_right
      · exact (disjoint_compl_right).mono inf_le_right inf_le_right
      · exact (hbc rfl).elim
    · exact (le_compl_iff_disjoint_right.mp (P.disjoint hij)).mono
        inf_le_left inf_le_left
  total := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.id_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
      ProjectionBand.bandProjection_inf, LinearMap.comp_apply,
      ProjectionBand.bandProjection_compl, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub]
    calc
      _ = ∑ i, (P.band i).bandProjection x := by
        apply Finset.sum_congr rfl
        intro i _
        abel
      _ = x := P.sum_apply x

/-- A sub-band projection absorbs its parent projection. -/
theorem apply_parent {P Q : ProjectionBand X} (h : Q ≤ P) (x : X) :
    Q.bandProjection (P.bandProjection x) = Q.bandProjection x := by
  have heq : Q ⊓ P = Q := inf_eq_left.mpr h
  have hm := congrArg (fun T : X →ₗ[ℝ] X => T x)
    (ProjectionBand.bandProjection_inf Q P)
  simpa [heq] using hm.symm

/-- Any band projection is monotone. -/
theorem monotone (P : ProjectionBand X) : Monotone P.bandProjection :=
  Positive.monotone_iff.mpr (Positive.zero_le_iff.mp P.bandProjection_nonneg)

/-- Order intervals on a parent cell remain true on every sub-cell. -/
theorem interval_on_subband {P Q : ProjectionBand X} (hQP : Q ≤ P)
    {x u : X} {a b : ℝ}
    (hlo : a • P.bandProjection u ≤ P.bandProjection x)
    (hhi : P.bandProjection x ≤ b • P.bandProjection u) :
    a • Q.bandProjection u ≤ Q.bandProjection x ∧
      Q.bandProjection x ≤ b • Q.bandProjection u := by
  constructor
  · have h := monotone Q hlo
    simpa only [map_smul, apply_parent hQP] using h
  · have h := monotone Q hhi
    simpa only [map_smul, apply_parent hQP] using h

def cellSpan (P : LatticeBandPartition X) (u : X) : Submodule ℝ X :=
  Submodule.span ℝ (Set.range fun i => (P.band i).bandProjection u)

theorem mem_cellSpan (P : LatticeBandPartition X) (u : X) (i : P.Index) :
    (P.band i).bandProjection u ∈ P.cellSpan u :=
  Submodule.subset_span (Set.mem_range_self i)

theorem self_mem_cellSpan (P : LatticeBandPartition X) (u : X) :
    u ∈ P.cellSpan u := by
  have h : (∑ i, (P.band i).bandProjection u) ∈ P.cellSpan u :=
    Submodule.sum_mem _ fun i _ => P.mem_cellSpan u i
  simpa only [P.sum_apply] using h

theorem cellSpan_le_common_left (P Q : LatticeBandPartition X) (u : X) :
    P.cellSpan u ≤ (P.common Q).cellSpan u := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  change (P.band i).bandProjection u ∈ (P.common Q).cellSpan u
  have heq : (P.band i).bandProjection u =
      ∑ j, ((P.common Q).band (i, j)).bandProjection u := by
    simp only [common, ProjectionBand.bandProjection_inf, LinearMap.comp_apply]
    rw [← map_sum, Q.sum_apply]
  rw [heq]
  exact Submodule.sum_mem _ fun j _ => (P.common Q).mem_cellSpan u (i, j)

theorem cellSpan_le_common_right (P Q : LatticeBandPartition X) (u : X) :
    Q.cellSpan u ≤ (P.common Q).cellSpan u := by
  apply Submodule.span_le.mpr
  rintro x ⟨j, rfl⟩
  change (Q.band j).bandProjection u ∈ (P.common Q).cellSpan u
  have heq : (Q.band j).bandProjection u =
      ∑ i, ((P.common Q).band (i, j)).bandProjection u := by
    simp only [common, inf_comm (P.band _) (Q.band _),
      ProjectionBand.bandProjection_inf, LinearMap.comp_apply]
    rw [← map_sum, P.sum_apply]
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => (P.common Q).mem_cellSpan u (i, j)

/-- Each bisection halves the width of all scalar order intervals. -/
theorem halve_intervals [HasPrincipalProjectionProperty X]
    (P : LatticeBandPartition X) (x u : X) (a : P.Index → ℝ) (δ : ℝ)
    (h : ∀ i, a i • (P.band i).bandProjection u ≤ (P.band i).bandProjection x ∧
      (P.band i).bandProjection x ≤ (a i + δ) • (P.band i).bandProjection u) :
    ∃ Q : LatticeBandPartition X, ∃ b : Q.Index → ℝ,
      ∀ i, b i • (Q.band i).bandProjection u ≤ (Q.band i).bandProjection x ∧
        (Q.band i).bandProjection x ≤
          (b i + δ / 2) • (Q.band i).bandProjection u := by
  let cut : P.Index → ProjectionBand X := fun i =>
    (exists_bandProjection_threshold x u (a i + δ / 2)).choose
  have hcut (i : P.Index) :
      (a i + δ / 2) • (cut i).bandProjection u ≤ (cut i).bandProjection x ∧
      (cut i)ᶜ.bandProjection x ≤ (a i + δ / 2) • (cut i)ᶜ.bandProjection u :=
    (exists_bandProjection_threshold x u (a i + δ / 2)).choose_spec
  let Q := P.split cut
  let b : Q.Index → ℝ := fun ib => a ib.1 + if ib.2 then δ / 2 else 0
  refine ⟨Q, b, ?_⟩
  rintro ⟨i, t⟩
  have hparent : Q.band (i, t) ≤ P.band i := inf_le_left
  have hp := interval_on_subband hparent (h i).1 (h i).2
  cases t
  · have hsub : Q.band (i, false) ≤ (cut i)ᶜ := inf_le_right
    have hh := monotone (Q.band (i, false)) (hcut i).2
    have hhi : (Q.band (i, false)).bandProjection x ≤
        (a i + δ / 2) • (Q.band (i, false)).bandProjection u := by
      simpa only [map_smul, apply_parent hsub] using hh
    simpa only [b, Bool.false_eq_true, ↓reduceIte, add_zero] using ⟨hp.1, hhi⟩
  · have hsub : Q.band (i, true) ≤ cut i := inf_le_right
    have hh := monotone (Q.band (i, true)) (hcut i).1
    have hlo : (a i + δ / 2) • (Q.band (i, true)).bandProjection u ≤
        (Q.band (i, true)).bandProjection x := by
      simpa only [map_smul, apply_parent hsub] using hh
    have hab : a i + δ / 2 + δ / 2 = a i + δ := by ring
    simpa only [b, ↓reduceIte, hab] using ⟨hlo, hp.2⟩

/-- Dyadic spectral approximation keeps quantitative order error rather than
changing to a principal-ideal gauge norm. -/
theorem exists_dyadic_intervals [HasPrincipalProjectionProperty X]
    (x u : X) (hx : 0 ≤ x) (hxu : x ≤ u) (n : ℕ) :
    ∃ P : LatticeBandPartition X, ∃ a : P.Index → ℝ,
      ∀ i, a i • (P.band i).bandProjection u ≤ (P.band i).bandProjection x ∧
        (P.band i).bandProjection x ≤
          (a i + (1 / 2 : ℝ) ^ n) • (P.band i).bandProjection u := by
  induction n with
  | zero =>
    refine ⟨trivial, fun _ => 0, ?_⟩
    intro i
    have ht (z : X) : ((trivial (X := X)).band i).bandProjection z = z :=
      ProjectionBand.bandProjection_eq_of_mem _ (by trivial)
    simpa only [ht, zero_smul, pow_zero, zero_add, one_smul] using ⟨hx, hxu⟩
  | succ n ih =>
    obtain ⟨P, a, ha⟩ := ih
    obtain ⟨Q, b, hb⟩ := halve_intervals P x u a ((1 / 2 : ℝ) ^ n) ha
    refine ⟨Q, b, ?_⟩
    intro i
    simpa only [pow_succ, div_eq_mul_inv, one_div, one_mul] using hb i

/-- The lower endpoint sum of cell intervals gives a single approximant with
the same order error. -/
theorem order_error_of_intervals (P : LatticeBandPartition X)
    (x u : X) (a : P.Index → ℝ) (δ : ℝ)
    (h : ∀ i, a i • (P.band i).bandProjection u ≤ (P.band i).bandProjection x ∧
      (P.band i).bandProjection x ≤ (a i + δ) • (P.band i).bandProjection u) :
    let y := ∑ i, a i • (P.band i).bandProjection u
    y ∈ P.cellSpan u ∧ 0 ≤ x - y ∧ x - y ≤ δ • u := by
  dsimp only
  refine ⟨Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (P.mem_cellSpan u i), ?_, ?_⟩
  · apply sub_nonneg.mpr
    calc
      _ ≤ ∑ i, (P.band i).bandProjection x := Finset.sum_le_sum fun i _ => (h i).1
      _ = x := P.sum_apply x
  · apply sub_le_iff_le_add.mpr
    calc
      x = ∑ i, (P.band i).bandProjection x := (P.sum_apply x).symm
      _ ≤ ∑ i, (a i + δ) • (P.band i).bandProjection u :=
        Finset.sum_le_sum fun i _ => (h i).2
      _ = δ • u + ∑ i, a i • (P.band i).bandProjection u := by
        simp only [add_smul, Finset.sum_add_distrib, ← Finset.smul_sum, P.sum_apply]
        exact add_comm _ _

end LatticeBandPartition

section Normed

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E] [HasPrincipalProjectionProperty E]

open LatticeBandPartition

/-- Positive vectors dominated by a common majorant admit arbitrarily close
finite spectral approximations in the original lattice norm. -/
theorem exists_positive_spectral_approximation (x u : E)
    (hx : 0 ≤ x) (hxu : x ≤ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : LatticeBandPartition E, ∃ y ∈ P.cellSpan u, ‖x - y‖ < ε := by
  have hu : 0 ≤ u := hx.trans hxu
  have hden : 0 < ‖u‖ + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hden)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨P, a, ha⟩ := exists_dyadic_intervals x u hx hxu n
  obtain ⟨hy, he0, he⟩ := order_error_of_intervals P x u a ((1 / 2 : ℝ) ^ n) ha
  refine ⟨P, ∑ i, a i • (P.band i).bandProjection u, hy, ?_⟩
  have hp : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hnorm : ‖x - ∑ i, a i • (P.band i).bandProjection u‖ ≤
      (1 / 2 : ℝ) ^ n * ‖u‖ := by
    calc
      _ ≤ ‖((1 / 2 : ℝ) ^ n) • u‖ := by
        apply norm_le_norm_of_abs_le_abs
        rw [abs_of_nonneg he0, abs_of_nonneg (smul_nonneg hp hu)]
        exact he
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
  have hsmall := (lt_div_iff₀ hden).mp hn
  nlinarith

/-- Signed vectors use the same positive majorant, by separately approximating
their positive and negative parts and taking a common band refinement. -/
theorem exists_spectral_approximation_of_abs_le (x u : E)
    (hxu : |x| ≤ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : LatticeBandPartition E, ∃ y ∈ P.cellSpan u, ‖x - y‖ < ε := by
  obtain ⟨P, p, hp, hep⟩ := exists_positive_spectral_approximation x⁺ u
    (posPart_nonneg x) ((posPart_le_abs x).trans hxu) (half_pos hε)
  obtain ⟨Q, q, hq, heq⟩ := exists_positive_spectral_approximation x⁻ u
    (negPart_nonneg x) ((negPart_le_abs x).trans hxu) (half_pos hε)
  refine ⟨P.common Q, p - q, Submodule.sub_mem _
    (P.cellSpan_le_common_left Q u hp) (P.cellSpan_le_common_right Q u hq), ?_⟩
  have he : x - (p - q) = (x⁺ - p) - (x⁻ - q) := by
    calc
      x - (p - q) = (x⁺ - x⁻) - (p - q) := by rw [posPart_sub_negPart]
      _ = _ := by abel
  rw [he]
  exact (norm_sub_le _ _).trans_lt (by linarith)

/-- A finite family shares one common finite band partition, with each
approximation error preserved exactly through refinement. -/
theorem exists_spectral_approximation_finset {ι : Type*} (s : Finset ι)
    (x : ι → E) (u : E) (hxu : ∀ i ∈ s, |x i| ≤ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : LatticeBandPartition E,
      ∀ i ∈ s, ∃ y ∈ P.cellSpan u, ‖x i - y‖ < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨trivial, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨P, hP⟩ := ih (fun j hj => hxu j (Finset.mem_insert_of_mem hj))
    obtain ⟨Q, q, hq, heq⟩ := exists_spectral_approximation_of_abs_le (x i) u
      (hxu i (Finset.mem_insert_self i s)) hε
    refine ⟨P.common Q, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨q, P.cellSpan_le_common_right Q u hq, heq⟩
    · obtain ⟨p, hp, hep⟩ := hP j hj
      exact ⟨p, P.cellSpan_le_common_left Q u hp, hep⟩

/-- Simultaneous finite disjoint spectral approximation. The common majorant
is the finite sum of lattice absolute values, so no extra domination hypothesis
is required. The finite-span correction can consume this result directly. -/
theorem exists_finite_disjoint_approximation {ι : Type*} [Fintype ι]
    (x : ι → E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : LatticeBandPartition E) (u : E),
      (∀ j, 0 ≤ (P.band j).bandProjection u) ∧
      (Pairwise fun j k => IsVLDisjoint ((P.band j).bandProjection u)
        ((P.band k).bandProjection u)) ∧
      ∀ i, ∃ y ∈ P.cellSpan u, ‖x i - y‖ < ε := by
  classical
  let u := ∑ i, |x i|
  have hu : 0 ≤ u := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hxu : ∀ i ∈ (Finset.univ : Finset ι), |x i| ≤ u := by
    intro i hi
    exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) hi
  obtain ⟨P, hP⟩ := exists_spectral_approximation_finset Finset.univ x u hxu hε
  exact ⟨P, u, P.positive hu, P.pairwise_disjoint u,
    fun i => hP i (Finset.mem_univ i)⟩

end Normed

end ComplementedSubspace
