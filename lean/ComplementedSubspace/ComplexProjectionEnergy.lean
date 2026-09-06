import ComplementedSubspace.FrameProjectionNorm
import Mathlib.Analysis.Complex.Norm

/-! Radial energy perturbation works for complex coordinates because the norm
is Lipschitz. For a real orthogonal matrix, the complex Pythagorean identity is
the sum of its real and imaginary Pythagorean identities. -/

noncomputable section
open scoped BigOperators ENNReal
open Matrix WithLp

namespace ComplementedSubspace

theorem finite_projection_norm_energy_bound {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] {p : ℝ} (hp : 2 ≤ p) (x a : ι → E)
    (hx : ∀ i, ‖x i‖ ≤ 1) (ha : ∀ i, ‖a i‖ ≤ 1)
    (horth : (∑ i, ‖a i‖ ^ 2) + (∑ i, ‖x i - a i‖ ^ 2) = ∑ i, ‖x i‖ ^ 2) :
    (∑ i, ‖a i‖ ^ p) ≤ (∑ i, ‖x i‖ ^ p) +
      (9 / 4 : ℝ) * Fintype.card ι * (p - 2) ^ 2 := by
  have hcoord (i : ι) :
      ‖a i‖ ^ p - ‖x i‖ ^ p ≤ ‖a i‖ ^ 2 - ‖x i‖ ^ 2 +
        ‖x i - a i‖ ^ 2 + (9 / 4 : ℝ) * (p - 2) ^ 2 := by
    have hlip := powerEnergyDifference_lipschitz hp
      (show ‖a i‖ ∈ Set.Icc (0 : ℝ) 1 from ⟨norm_nonneg _, ha i⟩)
      (show ‖x i‖ ∈ Set.Icc (0 : ℝ) 1 from ⟨norm_nonneg _, hx i⟩)
    have habs : |powerEnergyDifference p ‖a i‖ - powerEnergyDifference p ‖x i‖| ≤
        3 * (p - 2) * ‖x i - a i‖ := by
      refine hlip.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ 3 * (p - 2))
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le (a i) (x i)
    have hsq := sq_nonneg (‖x i - a i‖ - 3 / 2 * (p - 2))
    have hu := (abs_le.mp habs).2
    simp only [powerEnergyDifference] at hu
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoord i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  nlinarith

def complexPEnergy {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℂ) : ℝ :=
  ∑ i, ‖x i‖ ^ p

theorem complexPEnergy_nonneg {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℂ) :
    0 ≤ complexPEnergy p x :=
  Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _

theorem complexPEnergy_real_smul {ι : Type*} [Fintype ι] (p c : ℝ) (x : ι → ℂ) :
    complexPEnergy p (c • x) = |c| ^ p * complexPEnergy p x := by
  simp only [complexPEnergy, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), Finset.mul_sum]

def complexifyMatrix {ι κ : Type*} (Q : Matrix ι κ ℝ) : Matrix ι κ ℂ :=
  Q.map Complex.ofReal

@[simp] theorem complexifyMatrix_apply {ι κ : Type*} (Q : Matrix ι κ ℝ) (i : ι) (j : κ) :
    complexifyMatrix Q i j = (Q i j : ℂ) := rfl

theorem complexifyMatrix_mulVec_re {ι κ : Type*} [Fintype κ]
    (Q : Matrix ι κ ℝ) (x : κ → ℂ) (i : ι) :
    ((complexifyMatrix Q *ᵥ x) i).re = (Q *ᵥ fun j => (x j).re) i := by
  simp [Matrix.mulVec, dotProduct, Complex.mul_re]

theorem complexifyMatrix_mulVec_im {ι κ : Type*} [Fintype κ]
    (Q : Matrix ι κ ℝ) (x : κ → ℂ) (i : ι) :
    ((complexifyMatrix Q *ᵥ x) i).im = (Q *ᵥ fun j => (x j).im) i := by
  simp [Matrix.mulVec, dotProduct, Complex.mul_im]

theorem complexifyMatrix_pythagorean {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℝ) (hQsym : Q.transpose = Q) (hQid : Q * Q = Q)
    (x : ι → ℂ) :
    (∑ i, ‖(complexifyMatrix Q *ᵥ x) i‖ ^ 2) +
      (∑ i, ‖x i - (complexifyMatrix Q *ᵥ x) i‖ ^ 2) = ∑ i, ‖x i‖ ^ 2 := by
  have hre := symmetric_idempotent_pythagorean Q hQsym hQid (fun i => (x i).re)
  have him := symmetric_idempotent_pythagorean Q hQsym hQid (fun i => (x i).im)
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    complexifyMatrix_mulVec_re, complexifyMatrix_mulVec_im, Finset.sum_add_distrib, ← pow_two]
  linarith

theorem norm_coordinate_le_one_of_sum_sq_le {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] (x : ι → E) (hx : (∑ i, ‖x i‖ ^ 2) ≤ 1)
    (i : ι) : ‖x i‖ ≤ 1 := by
  have hi : ‖x i‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖x j‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (x i)]

theorem fin_four_complexEnergy_lower {p : ℝ} (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (x : Fin 4 → ℂ) (hx : (∑ i, ‖x i‖ ^ 2) = 1) :
    (1 / 2 : ℝ) ≤ complexPEnergy p x := by
  simpa only [finitePEnergy, abs_of_nonneg (norm_nonneg _), complexPEnergy] using
    fin_four_energy_lower hp hp3 (fun i => ‖x i‖) hx

theorem fin_four_complex_projection_energy_bound {p : ℝ} (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (Q : Matrix (Fin 4) (Fin 4) ℝ) (hQsym : Q.transpose = Q) (hQid : Q * Q = Q)
    (x : Fin 4 → ℂ) (hx : (∑ i, ‖x i‖ ^ 2) = 1) :
    complexPEnergy p (complexifyMatrix Q *ᵥ x) ≤
      (1 + 18 * (p - 2) ^ 2) * complexPEnergy p x := by
  have horth := complexifyMatrix_pythagorean Q hQsym hQid x
  have hsum0 : 0 ≤ ∑ i, ‖x i - (complexifyMatrix Q *ᵥ x) i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQx : (∑ i, ‖(complexifyMatrix Q *ᵥ x) i‖ ^ 2) ≤ 1 := by linarith
  have henergy := finite_projection_norm_energy_bound hp x (complexifyMatrix Q *ᵥ x)
    (norm_coordinate_le_one_of_sum_sq_le x hx.le)
    (norm_coordinate_le_one_of_sum_sq_le (complexifyMatrix Q *ᵥ x) hQx) horth
  have hlower := fin_four_complexEnergy_lower hp hp3 x hx
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at henergy
  change complexPEnergy p (complexifyMatrix Q *ᵥ x) ≤ complexPEnergy p x +
    9 * (p - 2) ^ 2 at henergy
  nlinarith [sq_nonneg (p - 2)]

end ComplementedSubspace
