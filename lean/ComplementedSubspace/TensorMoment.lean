import ComplementedSubspace.HilbertOverlap
import Mathlib.Tactic.Module

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace ComplementedSubspace

/-- Real polarization turns a diagonal quadratic bound into the sharp mixed bound.
No positivity or finite-dimensional spectral theorem is needed. -/
theorem symmetric_bilinear_norm_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] F) (hB : ∀ x y, B x y = B y x)
    (R : ℝ) (hR : 0 ≤ R) (hdiag : ∀ x, ‖B x x‖ ≤ R * ‖x‖ ^ 2)
    (x y : E) : ‖B x y‖ ≤ R * ‖x‖ * ‖y‖ := by
  have hbase (u v : E) : ‖B u v‖ ≤ R / 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have hid : (4 : ℝ) • B u v = B (u + v) (u + v) - B (u - v) (u - v) := by
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, hB v u]
      module
    have hn := norm_sub_le (B (u + v) (u + v)) (B (u - v) (u - v))
    rw [← hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hn
    have hp := parallelogram_law_with_norm ℝ u v
    have hd1 := hdiag (u + v)
    have hd2 := hdiag (u - v)
    nlinarith
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h := hbase (‖x‖⁻¹ • x) (‖y‖⁻¹ • y)
  have hnx : ‖‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, hxpos.ne']
  have hny : ‖‖y‖⁻¹ • y‖ = 1 := by simp [norm_smul, hypos.ne']
  rw [hnx, hny] at h
  simp only [map_smul, LinearMap.smul_apply, norm_smul, norm_inv, norm_norm] at h
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt (mul_pos hxpos hypos))
  field_simp at hmul
  nlinarith

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A matrix as a genuine Euclidean vector, for its Hilbert--Schmidt norm. -/
def hsVector (A : Matrix m n ℝ) : EuclideanSpace ℝ (m × n) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

lemma hsVector_norm_sq (A : Matrix m n ℝ) : ‖hsVector A‖ ^ 2 = hsSq A := by
  simp only [hsVector, EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply,
    Fintype.sum_prod_type, hsSq]

def hsVectorLinear : Matrix m n ℝ →ₗ[ℝ] EuclideanSpace ℝ (m × n) where
  toFun := hsVector
  map_add' A B := by ext p; rfl
  map_smul' r A := by ext p; rfl

lemma hsInner_sq_le (A B : Matrix m n ℝ) :
    hsInner A B ^ 2 ≤ hsSq A * hsSq B := by
  simpa only [hsInner, hsSq, Fintype.sum_prod_type] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun p : m × n => A p.1 p.2) (fun p : m × n => B p.1 p.2)

/-- The sharp polarization estimate, specialized to matrix Hilbert--Schmidt squares. -/
theorem rankOne_mixed_hsSq_bound
    (T : Matrix n n ℝ →ₗ[ℝ] Matrix m m ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hT : ∀ x : n → ℝ, hsSq (T (rankOne x)) ≤ r * (∑ i, x i ^ 2) ^ 2)
    (x y : n → ℝ) :
    hsSq (T (vecMulVec x y + vecMulVec y x)) ≤
      4 * r * (∑ i, x i ^ 2) * (∑ i, y i ^ 2) := by
  let V := (WithLp.linearEquiv 2 ℝ (n → ℝ)).toLinearMap
  let S : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n →ₗ[ℝ] Matrix n n ℝ :=
    (vecMulVecBilin ℝ ℝ).compl₁₂ V V
  let B := ((1 / 2 : ℝ) • (S + S.flip)).compr₂ (hsVectorLinear.comp T)
  have hsym (u v : EuclideanSpace ℝ n) : B u v = B v u := by
    simp only [B, LinearMap.compr₂_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.flip_apply, add_comm]
  have hdiag (u : EuclideanSpace ℝ n) :
      B u u = hsVector (T (rankOne (WithLp.ofLp u))) := by
    change hsVector (T ((1 / 2 : ℝ) • (vecMulVec (WithLp.ofLp u) (WithLp.ofLp u) +
      vecMulVec (WithLp.ofLp u) (WithLp.ofLp u)))) = _
    congr 2
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, rankOne]
    ring
  have hd (u : EuclideanSpace ℝ n) : ‖B u u‖ ≤ Real.sqrt r * ‖u‖ ^ 2 := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [hdiag, hsVector_norm_sq, mul_pow, Real.sq_sqrt hr,
      EuclideanSpace.real_norm_sq_eq]
    exact hT (WithLp.ofLp u)
  have h := symmetric_bilinear_norm_bound B hsym (Real.sqrt r)
    (Real.sqrt_nonneg _) hd (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  have hxy : B (WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      (1 / 2 : ℝ) • hsVector (T (vecMulVec x y + vecMulVec y x)) := by
    change hsVectorLinear (T ((1 / 2 : ℝ) • (vecMulVec x y + vecMulVec y x))) = _
    rw [map_smul, map_smul]
    rfl
  rw [hxy, norm_smul, Real.norm_eq_abs] at h
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
  have hh := pow_le_pow_left₀ (by positivity) h 2
  simp only [mul_pow] at hh
  rw [hsVector_norm_sq, Real.sq_sqrt hr] at hh
  simp only [EuclideanSpace.real_norm_sq_eq] at hh
  nlinarith

lemma tensor_hsSq_smul (r : ℝ) (A : Matrix n n ℝ) : hsSq (r • A) = r ^ 2 * hsSq A := by
  simp only [hsSq, Matrix.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]

lemma tensor_hsSq_add (A B : Matrix n n ℝ) :
    hsSq (A + B) = hsSq A + 2 * hsInner A B + hsSq B := by
  have hi (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by ring
  simp only [hsSq, hsInner, Matrix.add_apply, hi, Finset.sum_add_distrib,
    ← Finset.mul_sum]

lemma tensor_hsInner_smul_left (r : ℝ) (A B : Matrix n n ℝ) :
    hsInner (r • A) B = r * hsInner A B := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

lemma tensor_hsInner_smul_right (r : ℝ) (A B : Matrix n n ℝ) :
    hsInner A (r • B) = r * hsInner A B := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul,
    mul_left_comm (A _ _) r, ← Finset.mul_sum]

lemma tensor_hsSq_fromBlocks (A B C D : Matrix n n ℝ) :
    hsSq (Matrix.fromBlocks A B C D) = hsSq A + hsSq B + hsSq C + hsSq D := by
  simp [hsSq, Fintype.sum_sum_type, Finset.sum_add_distrib]
  ring

/-- The explicit two-by-two output block for one further real circle factor. -/
def circleBlock (A B H : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  (1 / 4 : ℝ) • Matrix.fromBlocks ((3 : ℝ) • A + B) H H (A + (3 : ℝ) • B)

lemma circleBlock_hsSq (A B H : Matrix n n ℝ) :
    hsSq (circleBlock A B H) =
      (10 * hsSq A + 10 * hsSq B + 12 * hsInner A B + 2 * hsSq H) / 16 := by
  rw [circleBlock, tensor_hsSq_smul, tensor_hsSq_fromBlocks,
    tensor_hsSq_add, tensor_hsSq_add, tensor_hsSq_smul, tensor_hsSq_smul,
    tensor_hsInner_smul_left, tensor_hsInner_smul_right]
  ring

theorem circleBlock_hsSq_bound (A B H : Matrix n n ℝ)
    (r a c : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hA : hsSq A ≤ r * a ^ 2) (hB : hsSq B ≤ r * c ^ 2)
    (hH : hsSq H ≤ 4 * r * a * c) :
    hsSq (circleBlock A B H) ≤ (5 / 8 : ℝ) * r * (a + c) ^ 2 := by
  have hi : hsInner A B ≤ r * a * c := by
    apply le_of_sq_le_sq _ (by positivity)
    calc
      hsInner A B ^ 2 ≤ hsSq A * hsSq B := hsInner_sq_le A B
      _ ≤ (r * a ^ 2) * (r * c ^ 2) :=
        mul_le_mul hA hB (hsSq_nonneg _) (by positivity)
      _ = (r * a * c) ^ 2 := by ring
  rw [circleBlock_hsSq]
  nlinarith

/-- Tensoring a matrix map with the real circle moment map, written in blocks. -/
def circleLift (T : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℝ →ₗ[ℝ] Matrix (n ⊕ n) (n ⊕ n) ℝ where
  toFun M := circleBlock (T (M.submatrix Sum.inl Sum.inl))
    (T (M.submatrix Sum.inr Sum.inr))
    (T (M.submatrix Sum.inl Sum.inr + M.submatrix Sum.inr Sum.inl))
  map_add' M N := by
    ext i j
    cases i <;> cases j <;>
      simp [circleBlock, Matrix.submatrix_add, map_add] <;> ring
  map_smul' r M := by
    ext i j
    cases i <;> cases j <;>
      simp [circleBlock, Matrix.submatrix_smul, ← smul_add, map_smul] <;> ring

/-- The induction step gives the exact factor `5/8` for every input vector. -/
theorem circleLift_rankOne_bound
    (T : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hT : ∀ x : n → ℝ, hsSq (T (rankOne x)) ≤ r * (∑ i, x i ^ 2) ^ 2)
    (b : n ⊕ n → ℝ) :
    hsSq (circleLift T (rankOne b)) ≤
      (5 / 8 : ℝ) * r * (∑ i, b i ^ 2) ^ 2 := by
  let x : n → ℝ := fun i => b (Sum.inl i)
  let y : n → ℝ := fun i => b (Sum.inr i)
  change hsSq (circleBlock (T (rankOne x)) (T (rankOne y))
    (T (vecMulVec x y + vecMulVec y x))) ≤ _
  rw [Fintype.sum_sum_type]
  exact circleBlock_hsSq_bound _ _ _ r (∑ i, x i ^ 2) (∑ i, y i ^ 2)
    hr (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hT x) (hT y)
    (rankOne_mixed_hsSq_bound T r hr hT x y)

/-- Binary tensor coordinates; the zero-fold space has dimension one. -/
def MomentIndex : ℕ → Type
  | 0 => Unit
  | k + 1 => MomentIndex k ⊕ MomentIndex k

instance momentIndexFintype : (k : ℕ) → Fintype (MomentIndex k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => @instFintypeSum (MomentIndex k) (MomentIndex k)
      (momentIndexFintype k) (momentIndexFintype k)

instance momentIndexDecidableEq (k : ℕ) : DecidableEq (MomentIndex k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ k ih =>
    letI : DecidableEq (MomentIndex k) := ih
    exact inferInstanceAs (DecidableEq (MomentIndex k ⊕ MomentIndex k))

/-- The real circle moment map tensor power, without abstract tensor products. -/
def tensorMoment : (k : ℕ) →
    Matrix (MomentIndex k) (MomentIndex k) ℝ →ₗ[ℝ]
      Matrix (MomentIndex k) (MomentIndex k) ℝ
  | 0 => LinearMap.id
  | k + 1 => circleLift (tensorMoment k)

/-- Exact arbitrary-tensor rank-one bound, obtained by real polarization and induction. -/
theorem tensorMoment_rankOne_bound (k : ℕ) (b : MomentIndex k → ℝ) :
    hsSq (tensorMoment k (rankOne b)) ≤
      (5 / 8 : ℝ) ^ k * (∑ i, b i ^ 2) ^ 2 := by
  induction k with
  | zero => simp [tensorMoment, hsSq_rankOne]
  | succ k ih =>
    change hsSq (circleLift (tensorMoment k) (rankOne b)) ≤
      (5 / 8 : ℝ) ^ (k + 1) * (∑ i : MomentIndex k ⊕ MomentIndex k, b i ^ 2) ^ 2
    have h := circleLift_rankOne_bound (tensorMoment k) ((5 / 8 : ℝ) ^ k)
      (by positivity) ih b
    rw [pow_succ, mul_comm ((5 / 8 : ℝ) ^ k) (5 / 8)]
    exact h

/-- The full deterministic paired-column estimate, with the tensor hypothesis discharged. -/
theorem tensor_paired_column_moments_bound (k : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B V : Matrix (MomentIndex k) ι ℝ) :
    (∑ i, ∑ j,
      hsInner (rankOne (fun l => B l i))
        (tensorMoment k (rankOne (fun l => B l j))) *
      hsInner (rankOne (fun l => V l i))
        (tensorMoment k (rankOne (fun l => V l j)))) ≤
      (Fintype.card ι : ℝ) * (‖B‖ * ‖V‖) ^ 4 * (5 / 8 : ℝ) ^ k :=
  paired_column_moments_bound B V (tensorMoment k) ((5 / 8 : ℝ) ^ k)
    (by positivity) (tensorMoment_rankOne_bound k)

end ComplementedSubspace
