import ComplementedSubspace.ProductFrameSymmetry
import ComplementedSubspace.FrameCoefficientNorm
import ComplementedSubspace.FiniteHilbertAverage
import Mathlib.LinearAlgebra.Trace

noncomputable section
namespace ComplementedSubspace

theorem frameSymmetry_pairing (n : ℕ) (u : FrameIndex n)
    (b c : MomentIndex n → ℝ) :
    (∑ i, frameSymmetry n u b i * frameSymmetry n u c i) = ∑ i, b i * c i := by
  rw [← productFrameEval_covariance, ← productFrameEval_covariance]
  calc
    _ = finiteAverage (fun s => productFrameEval n b (frameRowPerm n u s) *
        productFrameEval n c (frameRowPerm n u s)) := by
      congr 1
      funext s
      rw [productFrameEval_symmetry, productFrameEval_symmetry]
      have h : frameRowSign n u s ^ 2 = 1 := by
        calc
          _ = |frameRowSign n u s| ^ 2 := (sq_abs _).symm
          _ = 1 := by rw [frameRowSign_abs]; norm_num
      calc
        _ = frameRowSign n u s ^ 2 * (productFrameEval n b (frameRowPerm n u s) *
            productFrameEval n c (frameRowPerm n u s)) := by ring
        _ = _ := by rw [h, one_mul]
    _ = _ := finiteAverage_equiv (frameRowPerm n u)
      (fun s => productFrameEval n b s * productFrameEval n c s)

def frameSymmetryIsometry (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 0 < p) (u : FrameIndex n) : FrameCoefficient n p →ₗᵢ[ℝ] FrameCoefficient n p where
  toLinearMap :=
    { toFun := frameSymmetry n u
      map_add' := frameSymmetry_add n u
      map_smul' := frameSymmetry_smul n u }
  norm_map' b := by
    rw [frameCoefficient_norm_eq_average n p hp, frameCoefficient_norm_eq_average n p hp]
    exact congrArg (fun x : ℝ => x ^ (1 / p)) (productFrameEval_symmetry_energy n u b p)

def frameSymmetryEquiv (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 0 < p) (u : FrameIndex n) : FrameCoefficient n p ≃ₗᵢ[ℝ] FrameCoefficient n p :=
  LinearIsometryEquiv.ofSurjective (frameSymmetryIsometry n p hp u)
    (LinearMap.injective_iff_surjective.mp (frameSymmetryIsometry n p hp u).injective)

theorem frameSymmetryEquiv_apply (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 0 < p) (u : FrameIndex n) (b : FrameCoefficient n p) :
    frameSymmetryEquiv n p hp u b = frameSymmetry n u b := rfl

theorem frameSymmetryEquiv_inverse_coordinate (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) (u : FrameIndex n)
    (b : FrameCoefficient n p) (i : MomentIndex n) :
    (frameSymmetryEquiv n p hp u).symm b i =
      ∑ k, frameSymmetry n u (Pi.single i 1) k * b k := by
  let c : FrameCoefficient n p := (frameSymmetryEquiv n p hp u).symm b
  have hc : frameSymmetry n u c = b := (frameSymmetryEquiv n p hp u).apply_symm_apply b
  have h := frameSymmetry_pairing n u (Pi.single i 1) c
  rw [hc] at h
  have hs : (∑ k, (Pi.single i 1 : MomentIndex n → ℝ) k * c k) = c i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [Pi.single_apply, hki]
    · simp
  rw [hs] at h
  exact h.symm

section CoordinateAlgebra

set_option allowUnsafeReducibility true in
attribute [local reducible] FrameCoefficient Matrix

theorem frameCoefficient_linear_apply (n : ℕ) (p : ℝ)
    (T : FrameCoefficient n p →ₗ[ℝ] FrameCoefficient n p)
    (b : FrameCoefficient n p) (k : MomentIndex n) :
    T b k = ∑ j, b j * T (Pi.single j 1) k := by
  have hb : (∑ j, b j • (Pi.single j 1 : FrameCoefficient n p)) = b := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single b
  calc
    T b k = T (∑ j, b j • (Pi.single j 1 : FrameCoefficient n p)) k := by rw [hb]
    _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem frameCoefficient_trace_eq_sum (n : ℕ) (p : ℝ)
    (T : FrameCoefficient n p →ₗ[ℝ] FrameCoefficient n p) :
    LinearMap.trace ℝ (FrameCoefficient n p) T = ∑ j, T (Pi.single j 1) j := by
  let b : Module.Basis (MomentIndex n) ℝ (FrameCoefficient n p) := Pi.basisFun ℝ _
  rw [LinearMap.trace_eq_matrix_trace ℝ b T]
  simp only [Matrix.trace, LinearMap.toMatrix_apply]
  simp [b, Pi.basisFun_apply, LinearMap.toMatrix'_apply]

end CoordinateAlgebra

/-- Averaging finite signed-swap conjugates gives exactly the scalar trace
operator; no Haar measure or invariant-inner-product theorem is used. -/
theorem frameSymmetry_twirl_coordinate (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (T : FrameCoefficient n p →ₗ[ℝ] FrameCoefficient n p)
    (x : FrameCoefficient n p) (i : MomentIndex n) :
    finiteAverage (fun u =>
      (frameSymmetryEquiv n p hp u).symm (T (frameSymmetryEquiv n p hp u x)) i) =
      ((2 : ℝ) ^ n)⁻¹ * LinearMap.trace ℝ (FrameCoefficient n p) T * x i := by
  have hT (u : FrameIndex n) (k : MomentIndex n) :
      T (frameSymmetryEquiv n p hp u x) k =
        ∑ j, (frameSymmetryEquiv n p hp u x) j * T (Pi.single j 1) k :=
    frameCoefficient_linear_apply n p T (frameSymmetryEquiv n p hp u x) k
  simp only [frameSymmetryEquiv_inverse_coordinate, hT,
    Finset.mul_sum, finiteAverage_sum]
  let M : MomentIndex n → MomentIndex n → ℝ := fun k j => T (Pi.single j 1) k
  let y : MomentIndex n → ℝ := x
  change (∑ k, ∑ j, finiteAverage (fun u =>
    frameSymmetry n u (Pi.single i 1) k *
      (frameSymmetry n u y j * M k j))) =
    ((2 : ℝ) ^ n)⁻¹ * LinearMap.trace ℝ (FrameCoefficient n p) T * y i
  have hav (k j : MomentIndex n) : finiteAverage (fun u =>
      frameSymmetry n u (Pi.single i 1) k *
        (frameSymmetry n u y j * M k j)) =
      M k j *
        finiteAverage (fun u => frameSymmetry n u (Pi.single i 1) k * frameSymmetry n u y j) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using finiteAverage_mul
      (M k j)
      (fun u => frameSymmetry n u (Pi.single i 1) k * frameSymmetry n u y j)
  simp_rw [hav, frameSymmetry_covariance]
  have hs : (∑ k, (Pi.single i 1 : MomentIndex n → ℝ) k * y k) = y i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [hki]
    · simp
  rw [hs]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  have ht : LinearMap.trace ℝ (FrameCoefficient n p) T = ∑ j, M j j :=
    frameCoefficient_trace_eq_sum n p T
  rw [ht]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

end ComplementedSubspace
