import ComplementedSubspace.TheoremStatement
import Mathlib.Tactic.GCongr

/-!
# The ambient space is a real Banach lattice

The coordinate order on finite `PiLp` products and on dependent `lp` sums is
compatible with the existing norm, addition, and real scalar multiplication.
The finite-product construction is adapted from David Muñoz-Lahoz's BanLat
`Pi.lean`; the infinite-sum construction generalizes the scalar construction
in Jesús Illescas-Fiorito's BanLat `Examples/Ellp/Basic.lean` to varying normed
lattice fibers. The outer norm comparison uses Mathlib's `lp.norm_mono`.
-/

noncomputable section

open scoped ENNReal

namespace ComplementedSubspace

namespace LatticeSupport

section FiniteProduct

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)]

instance piLpLE : LE (PiLp p E) where
  le x y := ∀ i, x i ≤ y i

instance piLpLT : LT (PiLp p E) where
  lt x y := WithLp.ofLp x < WithLp.ofLp y

instance piLpMax : Max (PiLp p E) where
  max x y := WithLp.toLp p (fun i => x i ⊔ y i)

instance piLpMin : Min (PiLp p E) where
  min x y := WithLp.toLp p (fun i => x i ⊓ y i)

instance piLpLattice : Lattice (PiLp p E) :=
  Function.Injective.lattice (β := ∀ i, E i) WithLp.ofLp (WithLp.ofLp_injective p)
    Iff.rfl Iff.rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance piLpIsOrderedAddMonoid : IsOrderedAddMonoid (PiLp p E) :=
  Function.Injective.isOrderedAddMonoid (β := PiLp p E) (α := ∀ i, E i)
    WithLp.ofLp (fun _ _ => rfl) Iff.rfl

instance piLpHasSolidNorm [∀ i, HasSolidNorm (E i)] : HasSolidNorm (PiLp p E) where
  solid := fun x y h => by
    have hpt : ∀ i, ‖x i‖ ≤ ‖y i‖ := fun i => HasSolidNorm.solid (α := E i) (h i)
    rcases eq_or_ne p ∞ with hp | hp
    · subst hp
      simp only [PiLp.norm_eq_ciSup]
      exact ciSup_mono (Set.Finite.bddAbove (Set.finite_range _)) hpt
    · have hpos : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
      simp only [PiLp.norm_eq_sum hpos]
      apply Real.rpow_le_rpow
      · exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
      · exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (hpt i) hpos.le
      · exact one_div_nonneg.mpr hpos.le

instance piLpPosSMulMono [∀ i, NormedSpace ℝ (E i)] [∀ i, PosSMulMono ℝ (E i)] :
    PosSMulMono ℝ (PiLp p E) where
  smul_le_smul_of_nonneg_left := by
    intro a ha x y h i
    exact smul_le_smul_of_nonneg_left (h i) ha

end FiniteProduct

section DependentSum

variable {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, HasSolidNorm (E i)]

instance lpLE : LE (lp E p) where
  le x y := ∀ i, x i ≤ y i

instance lpLT : LT (lp E p) where
  lt x y := (x : ∀ i, E i) < (y : ∀ i, E i)

instance lpMax : Max (lp E p) where
  max x y := ⟨fun i => x i ⊔ y i,
    ((lp.memℓp x).norm.add (lp.memℓp y).norm).mono fun i => norm_sup_le_add (x i) (y i)⟩

instance lpMin : Min (lp E p) where
  min x y := ⟨fun i => x i ⊓ y i,
    ((lp.memℓp x).norm.add (lp.memℓp y).norm).mono fun i => norm_inf_le_add (x i) (y i)⟩

instance lpLattice : Lattice (lp E p) :=
  Function.Injective.lattice (β := ∀ i, E i) ((↑) : lp E p → ∀ i, E i)
    Subtype.val_injective Iff.rfl Iff.rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance lpIsOrderedAddMonoid : IsOrderedAddMonoid (lp E p) :=
  Function.Injective.isOrderedAddMonoid (β := lp E p) (α := ∀ i, E i)
    ((↑) : lp E p → ∀ i, E i) (fun _ _ => rfl) Iff.rfl

instance lpHasSolidNorm : HasSolidNorm (lp E p) where
  solid := fun x y h => by
    apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) Fact.out))
    intro i
    exact HasSolidNorm.solid (α := E i) (h i)

instance lpPosSMulMono [∀ i, NormedSpace ℝ (E i)] [∀ i, PosSMulMono ℝ (E i)] :
    PosSMulMono ℝ (lp E p) where
  smul_le_smul_of_nonneg_left := by
    intro a ha x y h i
    exact smul_le_smul_of_nonneg_left (h i) ha

end DependentSum

end LatticeSupport

/-- Each finite real block has the compatible coordinate Banach lattice order. -/
theorem block_hasRealBanachLatticeOrder (a : BlockParameters) (j : ℕ) :
    HasRealBanachLatticeOrder (Block a j) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The inherited norm on the actual dependent `ℓ²` sum is a Banach lattice norm. -/
theorem ambient_hasRealBanachLatticeOrder (a : BlockParameters) :
    HasRealBanachLatticeOrder (Ambient a) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end ComplementedSubspace
