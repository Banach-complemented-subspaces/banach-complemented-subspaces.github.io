import ComplementedSubspace.LpSubmodule
import Mathlib.Analysis.Normed.Lp.ProdLp

/-! Contractive head/tail restrictions and the exact two-term lp2 split. -/

noncomputable section
open scoped ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

section Restriction
variable {ι κ : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]

def lpRestrictLinear (f : κ → ι) (hf : Function.Injective f) :
    lp E 2 →ₗ[ℝ] lp (fun k => E (f k)) 2 where
  toFun x := ⟨fun k => x (f k), by
    change Memℓp (fun k => x (f k)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact ((lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).comp_injective hf⟩
  map_add' x y := by ext k; rfl
  map_smul' r x := by ext k; rfl

@[simp] theorem lpRestrictLinear_apply (f : κ → ι) (hf : Function.Injective f)
    (x : lp E 2) (k : κ) : lpRestrictLinear f hf x k = x (f k) := rfl

theorem lpRestrictLinear_norm_le (f : κ → ι) (hf : Function.Injective f) (x : lp E 2) :
    ‖lpRestrictLinear f hf x‖ ≤ ‖x‖ := by
  have hs := lp_two_hasSum_sq x
  have hr := lp_two_hasSum_sq (lpRestrictLinear f hf x)
  have h := hr.summable.tsum_le_tsum_of_inj f hf (fun i _ => sq_nonneg ‖x i‖)
    (fun _ => le_rfl) hs.summable
  change (∑' k, ‖lpRestrictLinear f hf x k‖ ^ 2) ≤ (∑' i, ‖x i‖ ^ 2) at h
  rw [hr.tsum_eq, hs.tsum_eq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

def lpRestrictCLM (f : κ → ι) (hf : Function.Injective f) :
    lp E 2 →L[ℝ] lp (fun k => E (f k)) 2 :=
  (lpRestrictLinear f hf).mkContinuous 1 (fun x => by
    simpa only [one_mul] using lpRestrictLinear_norm_le f hf x)

@[simp] theorem lpRestrictCLM_apply (f : κ → ι) (hf : Function.Injective f)
    (x : lp E 2) (k : κ) : lpRestrictCLM f hf x k = x (f k) := rfl

theorem lpRestrictCLM_norm_le (f : κ → ι) (hf : Function.Injective f) :
    ‖lpRestrictCLM (E := E) f hf‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Restriction

section HeadTail
variable {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

def lpHead (j : ℕ) : lp E 2 →L[ℝ] lp (fun i : Fin j => E i.val) 2 :=
  lpRestrictCLM Fin.val Fin.val_injective

def lpTail (j : ℕ) : lp E 2 →L[ℝ] lp (fun k => E (j + k)) 2 :=
  lpRestrictCLM (fun k => j + k) (fun _ _ h => Nat.add_left_cancel h)

@[simp] theorem lpHead_apply (j : ℕ) (x : lp E 2) (i : Fin j) : lpHead j x i = x i.val := rfl
@[simp] theorem lpTail_apply (j : ℕ) (x : lp E 2) (k : ℕ) : lpTail j x k = x (j + k) := rfl

theorem lpHead_norm_le (j : ℕ) : ‖lpHead (E := E) j‖ ≤ 1 := lpRestrictCLM_norm_le _ _
theorem lpTail_norm_le (j : ℕ) : ‖lpTail (E := E) j‖ ≤ 1 := lpRestrictCLM_norm_le _ _

theorem lpHead_norm_sq (j : ℕ) (x : lp E 2) :
    ‖lpHead j x‖ ^ 2 = ∑ i ∈ Finset.range j, ‖x i‖ ^ 2 := by
  rw [← (lp_two_hasSum_sq (lpHead j x)).tsum_eq, tsum_fintype]
  exact Fin.sum_univ_eq_sum_range (fun i => ‖x i‖ ^ 2) j

theorem lpHead_tail_norm_sq (j : ℕ) (x : lp E 2) :
    ‖x‖ ^ 2 = ‖lpHead j x‖ ^ 2 + ‖lpTail j x‖ ^ 2 := by
  have hx := lp_two_hasSum_sq x
  have ht := lp_two_hasSum_sq (lpTail j x)
  have h := hx.summable.sum_add_tsum_nat_add j
  rw [hx.tsum_eq, ← lpHead_norm_sq j x] at h
  have htail : (∑' k, ‖x (k + j)‖ ^ 2) = ‖lpTail j x‖ ^ 2 := by
    calc
      (∑' k, ‖x (k + j)‖ ^ 2) = ∑' k, ‖x (j + k)‖ ^ 2 := by
        apply tsum_congr
        intro k
        rw [Nat.add_comm k j]
      _ = ‖lpTail j x‖ ^ 2 := ht.tsum_eq
  rw [htail] at h
  exact h.symm

theorem lpHead_tail_skip_norm_sq (j : ℕ) (x : lp E 2) (hx : x j = 0) :
    ‖x‖ ^ 2 = ‖lpHead j x‖ ^ 2 + ‖lpTail (j + 1) x‖ ^ 2 := by
  have h := lpHead_tail_norm_sq (j + 1) x
  rw [lpHead_norm_sq, Finset.sum_range_succ, hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    add_zero, ← lpHead_norm_sq j x] at h
  exact h

/-- Splitting the kernel of one coordinate into its actual finite head and tail. -/
def lpKernelHeadTailIsometry (j : ℕ) :
    (lp.evalCLM ℝ E 2 j).ker →ₗᵢ[ℝ]
      WithLp 2 (lp (fun i : Fin j => E i.val) 2 × lp (fun k => E (j + 1 + k)) 2) where
  toFun x := WithLp.toLp 2 (lpHead j (x : lp E 2), lpTail (j + 1) (x : lp E 2))
  map_add' x y := by
    simp only [Submodule.coe_add, map_add, ← WithLp.toLp_add, Prod.mk_add_mk]
  map_smul' r x := by
    simp only [Submodule.coe_smul, map_smul, ← WithLp.toLp_smul, Prod.smul_mk, RingHom.id_apply]
  norm_map' x := by
    have h := lpHead_tail_skip_norm_sq j (x : lp E 2) x.property
    have hprod := WithLp.prod_norm_sq_eq_of_L2
      (WithLp.toLp 2 (lpHead j (x : lp E 2), lpTail (j + 1) (x : lp E 2)))
    change ‖x‖ ^ 2 = ‖lpHead j (x : lp E 2)‖ ^ 2 + ‖lpTail (j + 1) (x : lp E 2)‖ ^ 2 at h
    change ‖WithLp.toLp 2 (lpHead j (x : lp E 2), lpTail (j + 1) (x : lp E 2))‖ ^ 2 =
      ‖lpHead j (x : lp E 2)‖ ^ 2 + ‖lpTail (j + 1) (x : lp E 2)‖ ^ 2 at hprod
    change ‖WithLp.toLp 2 (lpHead j (x : lp E 2), lpTail (j + 1) (x : lp E 2))‖ = ‖x‖
    apply le_antisymm <;>
      nlinarith only [h, hprod, norm_nonneg x,
        norm_nonneg (WithLp.toLp 2 (lpHead j (x : lp E 2), lpTail (j + 1) (x : lp E 2)))]

end HeadTail

section ActualDiagonalRange
variable {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (P : ∀ i, E i →L[ℝ] E i) {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖P i‖ ≤ C)
    (hIdem : ∀ i, (P i).comp (P i) = P i)

def lpDiagonalRangeKernelProfileIsometry (j : ℕ) :
    (lpDiagonalRangeEval P hC hP hIdem j).ker →ₗᵢ[ℝ]
      (lp.evalCLM ℝ (fun i => (P i).range) 2 j).ker where
  toFun x := ⟨(lpDiagonalRangeEquiv P hC hP hIdem).symm x.val, x.property⟩
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp
  norm_map' x := (lpDiagonalRangeEquiv P hC hP hIdem).symm.norm_map x.val

/-- The exact head/tail isometric embedding for the complementary coordinate
kernel inside the actual infinite projection range. -/
def lpDiagonalRangeKernelHeadTailIsometry (j : ℕ) :
    (lpDiagonalRangeEval P hC hP hIdem j).ker →ₗᵢ[ℝ]
      WithLp 2 (lp (fun i : Fin j => (P i.val).range) 2 ×
        lp (fun k => (P (j + 1 + k)).range) 2) :=
  (lpKernelHeadTailIsometry j).comp (lpDiagonalRangeKernelProfileIsometry P hC hP hIdem j)

end ActualDiagonalRange
end ComplementedSubspace
