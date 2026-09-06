import ComplementedSubspace.ProductFrameLp

noncomputable section
namespace ComplementedSubspace

set_option allowUnsafeReducibility true in
attribute [local reducible] MomentIndex FrameIndex

/-- The four signed coordinate swaps, tensorized in coefficient coordinates.
Their labels use the same finite index as the four-point sampling frame. -/
def frameSymmetry : (n : ℕ) → FrameIndex n →
    (MomentIndex n → ℝ) → (MomentIndex n → ℝ)
  | 0, _, b => b
  | n + 1, u, b =>
    let a := frameSymmetry n u.2 (fun i => b (.inl i))
    let c := frameSymmetry n u.2 (fun i => b (.inr i))
    if u.1 = 0 then Sum.elim a c
    else if u.1 = 1 then Sum.elim a (-c)
    else if u.1 = 2 then Sum.elim c a
    else Sum.elim (-c) a

def localFrameRowPerm (r : Fin 4) : Equiv.Perm (Fin 4) :=
  if r = 0 then Equiv.refl _
  else if r = 1 then Equiv.swap 2 3
  else if r = 2 then Equiv.swap 0 1
  else (Equiv.swap 0 1).trans (Equiv.swap 2 3)

def localFrameRowSign (r s : Fin 4) : ℝ :=
  if r = 0 then 1
  else if r = 1 then (if s = 1 then -1 else 1)
  else if r = 2 then (if s = 3 then -1 else 1)
  else (if s = 0 ∨ s = 3 then -1 else 1)

def frameRowPerm : (n : ℕ) → FrameIndex n → Equiv.Perm (FrameIndex n)
  | 0, _ => Equiv.refl _
  | n + 1, u => Equiv.prodCongr (localFrameRowPerm u.1) (frameRowPerm n u.2)

def frameRowSign : (n : ℕ) → FrameIndex n → FrameIndex n → ℝ
  | 0, _, _ => 1
  | n + 1, u, s => localFrameRowSign u.1 s.1 * frameRowSign n u.2 s.2

theorem frameRowSign_abs (n : ℕ) (u s : FrameIndex n) : |frameRowSign n u s| = 1 := by
  induction n with
  | zero => norm_num [frameRowSign]
  | succ n ih =>
    simp only [frameRowSign, abs_mul, ih, mul_one]
    unfold localFrameRowSign
    split_ifs <;> norm_num

theorem productFrameEval_succ (n : ℕ) (b : MomentIndex (n + 1) → ℝ)
    (s : FrameIndex (n + 1)) :
    productFrameEval (n + 1) b s =
      realFrame s.1 0 * productFrameEval n (fun i => b (.inl i)) s.2 +
      realFrame s.1 1 * productFrameEval n (fun i => b (.inr i)) s.2 := by
  change (∑ i : MomentIndex n ⊕ MomentIndex n, _) = _
  rw [Fintype.sum_sum_type]
  simp only [realProductFrame, productFrameEval, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

theorem productFrameEval_neg (n : ℕ) (b : MomentIndex n → ℝ) (s : FrameIndex n) :
    productFrameEval n (-b) s = -productFrameEval n b s := by
  simp only [productFrameEval, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem productFrameEval_neg_fun (n : ℕ) (b : MomentIndex n → ℝ) (s : FrameIndex n) :
    productFrameEval n (fun i => -b i) s = -productFrameEval n b s :=
  productFrameEval_neg n b s

theorem productFrameEval_symmetry (n : ℕ) (u : FrameIndex n)
    (b : MomentIndex n → ℝ) (s : FrameIndex n) :
    productFrameEval n (frameSymmetry n u b) s =
      frameRowSign n u s * productFrameEval n b (frameRowPerm n u s) := by
  induction n with
  | zero => simp [frameSymmetry, frameRowSign, frameRowPerm]
  | succ n ih =>
    rcases u with ⟨r, u⟩
    rcases s with ⟨t, s⟩
    rw [productFrameEval_succ, productFrameEval_succ]
    fin_cases r <;> fin_cases t <;>
      norm_num [frameSymmetry, frameRowSign, frameRowPerm, localFrameRowPerm,
        localFrameRowSign, realFrame, productFrameEval_neg_fun, ih,
        Equiv.swap_apply_def, Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.vecHead, Matrix.vecTail] <;> ring

theorem finiteAverage_equiv {ι : Type*} [Fintype ι]
    (e : Equiv.Perm ι) (f : ι → ℝ) :
    finiteAverage (fun i => f (e i)) = finiteAverage f := by
  unfold finiteAverage
  rw [Equiv.sum_comp]

/-- Actual finite p-energy is unchanged by every tensor signed swap. -/
theorem productFrameEval_symmetry_energy (n : ℕ) (u : FrameIndex n)
    (b : MomentIndex n → ℝ) (p : ℝ) :
    finiteAverage (fun s => |productFrameEval n (frameSymmetry n u b) s| ^ p) =
      finiteAverage (fun s => |productFrameEval n b s| ^ p) := by
  simp_rw [productFrameEval_symmetry, abs_mul, frameRowSign_abs, one_mul]
  exact finiteAverage_equiv (frameRowPerm n u) (fun s => |productFrameEval n b s| ^ p)

theorem frameSymmetry_add (n : ℕ) (u : FrameIndex n) (b c : MomentIndex n → ℝ) :
    frameSymmetry n u (b + c) = frameSymmetry n u b + frameSymmetry n u c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases u with ⟨r, u⟩
    have hl (i : MomentIndex n) := congrFun
      (ih u (fun j => b (.inl j)) (fun j => c (.inl j))) i
    have hr (i : MomentIndex n) := congrFun
      (ih u (fun j => b (.inr j)) (fun j => c (.inr j))) i
    change ∀ i, frameSymmetry n u (fun j => b (.inl j) + c (.inl j)) i =
      frameSymmetry n u (fun j => b (.inl j)) i +
        frameSymmetry n u (fun j => c (.inl j)) i at hl
    change ∀ i, frameSymmetry n u (fun j => b (.inr j) + c (.inr j)) i =
      frameSymmetry n u (fun j => b (.inr j)) i +
        frameSymmetry n u (fun j => c (.inr j)) i at hr
    funext i
    cases i <;> fin_cases r <;>
      simp [frameSymmetry, Pi.add_apply, hl, hr, Fin.ext_iff] <;> ring

theorem frameSymmetry_smul (n : ℕ) (u : FrameIndex n) (r : ℝ)
    (b : MomentIndex n → ℝ) :
    frameSymmetry n u (r • b) = r • frameSymmetry n u b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases u with ⟨t, u⟩
    have hl (i : MomentIndex n) := congrFun (ih u (fun j => b (.inl j))) i
    have hr (i : MomentIndex n) := congrFun (ih u (fun j => b (.inr j))) i
    change ∀ i, frameSymmetry n u (fun j => r * b (.inl j)) i =
      r * frameSymmetry n u (fun j => b (.inl j)) i at hl
    change ∀ i, frameSymmetry n u (fun j => r * b (.inr j)) i =
      r * frameSymmetry n u (fun j => b (.inr j)) i at hr
    funext i
    cases i <;> fin_cases t <;>
      simp [frameSymmetry, Pi.smul_apply, smul_eq_mul, hl, hr, Fin.ext_iff]

def frameSymmetryLinear (n : ℕ) (u : FrameIndex n) :
    (MomentIndex n → ℝ) →ₗ[ℝ] (MomentIndex n → ℝ) where
  toFun := frameSymmetry n u
  map_add' := frameSymmetry_add n u
  map_smul' := frameSymmetry_smul n u

theorem finiteAverage_fin4 (f : Fin 4 → ℝ) :
    finiteAverage f = (f 0 + f 1 + f 2 + f 3) / 4 := by
  norm_num [finiteAverage, Fin.sum_univ_succ,
    show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  ring

theorem finiteAverage_neg {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    finiteAverage (fun i => -f i) = -finiteAverage f := by
  simp only [finiteAverage, Finset.sum_neg_distrib, mul_neg]

/-- Exact mixed covariance of the finite tensor signed-swap orbit. -/
theorem frameSymmetry_covariance (n : ℕ) (b c : MomentIndex n → ℝ)
    (i j : MomentIndex n) :
    finiteAverage (fun u => frameSymmetry n u b i * frameSymmetry n u c j) =
      if i = j then ((2 : ℝ) ^ n)⁻¹ * ∑ k, b k * c k else 0 := by
  induction n with
  | zero =>
    cases i
    cases j
    simp [frameSymmetry, finiteAverage, MomentIndex, FrameIndex, Fintype.card_unit]
  | succ n ih =>
    change finiteAverage (fun u : Fin 4 × FrameIndex n => _) = _
    rw [finiteAverage_prod, finiteAverage_fin4]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        norm_num [frameSymmetry, Fin.ext_iff, neg_mul_neg, ih,
          Fintype.sum_sum_type, MomentIndex, pow_succ]
        split_ifs <;> simp_all <;> ring
      | inr j =>
        norm_num [frameSymmetry, Fin.ext_iff, neg_mul, mul_neg, finiteAverage_neg,
          Sum.inl_ne_inr] <;> ring
    | inr i =>
      cases j with
      | inl j =>
        norm_num [frameSymmetry, Fin.ext_iff, neg_mul, mul_neg, finiteAverage_neg,
          Sum.inr_ne_inl] <;> ring
      | inr j =>
        norm_num [frameSymmetry, Fin.ext_iff, neg_mul_neg, ih,
          Fintype.sum_sum_type, MomentIndex, pow_succ]
        split_ifs <;> simp_all <;> ring

end ComplementedSubspace
