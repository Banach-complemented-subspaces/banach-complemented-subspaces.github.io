import ComplementedSubspace.SchauderDPR
import ComplementedSubspace.DPRIsomorphism
import Mathlib.Analysis.Normed.Module.RCLike.Extend

/-! Complex unconditional bases force real DPR for the same inherited norm.
We split each complex coordinate into its real and imaginary coordinates.
The dual realification is Mathlib's actual continuous dual isometry. -/

noncomputable section
open scoped BigOperators ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_complex_sum_smul_le_of_subsum_bound {ι : Type*} [Fintype ι]
    (v : ι → E) (K : ℝ) (hK : ∀ s : Finset ι, ‖∑ i ∈ s, v i‖ ≤ K)
    (θ : ι → ℂ) (hθ : ∀ i, ‖θ i‖ ≤ 1) :
    ‖∑ i, θ i • v i‖ ≤ 4 * K := by
  have hr := norm_sum_smul_le_of_subsum_bound v K hK (fun i => (θ i).re)
    (fun i => (Complex.abs_re_le_norm (θ i)).trans (hθ i))
  have hi := norm_sum_smul_le_of_subsum_bound v K hK (fun i => (θ i).im)
    (fun i => (Complex.abs_im_le_norm (θ i)).trans (hθ i))
  have heq : (∑ i, θ i • v i) =
      (∑ i, (θ i).re • v i) + Complex.I • (∑ i, (θ i).im • v i) := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => rw [← Complex.re_add_im (θ i)]
    rw [add_smul, mul_smul]
    simp only [Complex.coe_smul, smul_comm Complex.I]
  rw [heq]
  calc
    _ ≤ ‖∑ i, (θ i).re • v i‖ + ‖Complex.I • (∑ i, (θ i).im • v i)‖ := norm_add_le _ _
    _ = ‖∑ i, (θ i).re • v i‖ + ‖∑ i, (θ i).im • v i‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ 4 * K := by linarith

theorem summable_complex_smul_of_norm_le_one [CompleteSpace E] {ι : Type*}
    {v : ι → E} (hv : Summable v) (θ : ι → ℂ) (hθ : ∀ i, ‖θ i‖ ≤ 1) :
    Summable (fun i => θ i • v i) := by
  classical
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hv (ε / 8) (by positivity)
  refine ⟨s, ?_⟩
  intro t ht
  have hsub (u : Finset t) : ‖∑ i ∈ u, v i.val‖ ≤ ε / 8 := by
    have hu : Disjoint (u.image Subtype.val) s :=
      ht.mono_left (by intro i hi; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi; exact j.property)
    have h := (hs (u.image Subtype.val) hu).le
    have he : (∑ i ∈ u.image Subtype.val, v i) = ∑ i ∈ u, v i.val :=
      Finset.sum_image (by intro a _ b _ h; exact Subtype.ext h)
    rw [he] at h
    exact h
  have h := norm_complex_sum_smul_le_of_subsum_bound (fun i : t => v i.val)
    (ε / 8) hsub (fun i => θ i.val) (fun i => hθ i.val)
  have hsum : (∑ i : t, θ i.val • v i.val) = ∑ i ∈ t, θ i • v i :=
    by simpa only [Finset.univ_eq_attach] using Finset.sum_attach t (fun i => θ i • v i)
  rw [hsum] at h
  exact h.trans_lt (by linarith)

private theorem realPart_ratio_norm_le (z : ℂ) : ‖(z.re : ℂ) / z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  exact (div_le_one (norm_pos_iff.mpr hz)).mpr (Complex.abs_re_le_norm z)

private theorem realPart_ratio_smul (z : ℂ) (x : E) :
    ((z.re : ℂ) / z) • (z • x) = z.re • x := by
  by_cases hz : z = 0
  · simp [hz]
  rw [smul_smul, div_mul_cancel₀ _ hz, Complex.coe_smul]

theorem summable_real_part_coordinates [CompleteSpace E] {ι : Type*}
    (b : UnconditionalSchauderBasis ι ℂ E) (x : E) :
    Summable (fun i => (b.coord i x).re • b i) := by
  have h := summable_complex_smul_of_norm_le_one (b.expansion x).summable
    (fun i => ((b.coord i x).re : ℂ) / b.coord i x)
    (fun i => realPart_ratio_norm_le _)
  simpa only [realPart_ratio_smul] using h

private theorem complex_coordinate_split (z : ℂ) (x : E) :
    z.re • x + z.im • (Complex.I • x) = z • x := by
  rw [smul_comm (z.im) Complex.I, ← Complex.coe_smul z.re x,
    ← Complex.coe_smul z.im x, ← mul_smul, ← add_smul]
  congr 1
  simpa only [mul_comm Complex.I] using Complex.re_add_im z

def realifiedBasisVector {ι : Type*} (b : UnconditionalSchauderBasis ι ℂ E) : (ι ⊕ ι) → E :=
  Sum.elim (fun i => b i) (fun i => Complex.I • b i)

def realifiedBasisCoordinate {ι : Type*} (b : UnconditionalSchauderBasis ι ℂ E) :
    (ι ⊕ ι) → E →L[ℝ] ℝ :=
  Sum.elim
    (fun i => Complex.reCLM.comp ((b.coord i).restrictScalars ℝ))
    (fun i => Complex.imCLM.comp ((b.coord i).restrictScalars ℝ))

theorem hasSum_realifiedBasis [CompleteSpace E] {ι : Type*}
    (b : UnconditionalSchauderBasis ι ℂ E) (x : E) :
    HasSum (fun i => realifiedBasisCoordinate b i x • realifiedBasisVector b i) x := by
    have hr := summable_real_part_coordinates b x
    have hi : HasSum (fun i => (b.coord i x).im • (Complex.I • b i))
        (x - ∑' i, (b.coord i x).re • b i) := by
      have h := (b.expansion x).sub hr.hasSum
      convert h using 1
      ext i
      exact eq_sub_iff_add_eq.mpr (by
        rw [add_comm]
        exact complex_coordinate_split _ _)
    have h : HasSum
        (Sum.elim (fun i => (b.coord i x).re • b i)
          (fun i => (b.coord i x).im • (Complex.I • b i)))
        ((∑' i, (b.coord i x).re • b i) + (x - ∑' i, (b.coord i x).re • b i)) :=
      HasSum.sum hr.hasSum hi
    have heq : (fun i => realifiedBasisCoordinate b i x • realifiedBasisVector b i) =
        Sum.elim (fun i => (b.coord i x).re • b i)
          (fun i => (b.coord i x).im • (Complex.I • b i)) := by
      funext i
      cases i <;> rfl
    rw [heq]
    have hx : (∑' i, (b.coord i x).re • b i) +
        (x - ∑' i, (b.coord i x).re • b i) = x := by abel
    rw [hx] at h
    exact h

/-- Split each complex basis vector into itself and its multiple by i.
The index is a disjoint union; the same inherited norm is retained. -/
def realifiedUnconditionalSchauderBasis [CompleteSpace E] {ι : Type*}
    (b : UnconditionalSchauderBasis ι ℂ E) : UnconditionalSchauderBasis (ι ⊕ ι) ℝ E where
  basis := realifiedBasisVector b
  coord := realifiedBasisCoordinate b
  ortho := by
    classical
    intro i j
    cases i <;> cases j <;>
      simp [realifiedBasisCoordinate, realifiedBasisVector, b.ortho, Pi.single_apply, eq_comm, apply_ite]
  expansion := hasSum_realifiedBasis b

theorem hasRealDPR_of_complexUnconditionalSchauderBasis [CompleteSpace E] {ι : Type*}
    (b : UnconditionalSchauderBasis ι ℂ E) : HasDPRLocalUnconditionalStructure E :=
  hasDPR_of_unconditionalSchauderBasis (realifiedUnconditionalSchauderBasis b)

theorem not_hasComplexUnconditionalSchauderBasis_of_real_chiDPR_top [CompleteSpace E]
    (hE : chiDPR E = ⊤) : ¬ HasUnconditionalSchauderBasis ℂ E := by
  intro hBasis
  rcases hBasis with hfin | hinf
  · rcases hfin with ⟨n, ⟨b⟩⟩
    have h := hasRealDPR_of_complexUnconditionalSchauderBasis b
    change chiDPR E < ⊤ at h
    rw [hE] at h
    exact h.false
  · rcases hinf with ⟨b⟩
    have h := hasRealDPR_of_complexUnconditionalSchauderBasis b
    change chiDPR E < ⊤ at h
    rw [hE] at h
    exact h.false

theorem not_hasComplexUnconditionalSchauderBasis_of_real_equiv [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (hF : chiDPR F = ⊤) :
    ¬ HasUnconditionalSchauderBasis ℂ E := by
  intro hBasis
  rcases hBasis with hfin | hinf
  · rcases hfin with ⟨n, ⟨b⟩⟩
    have h := (hasRealDPR_of_complexUnconditionalSchauderBasis b).of_continuousLinearEquiv e
    change chiDPR F < ⊤ at h
    rw [hF] at h
    exact h.false
  · rcases hinf with ⟨b⟩
    have h := (hasRealDPR_of_complexUnconditionalSchauderBasis b).of_continuousLinearEquiv e
    change chiDPR F < ⊤ at h
    rw [hF] at h
    exact h.false

/-- The continuous complex dual, regarded as a real normed space, is the
actual continuous real dual with exactly the same norm. -/
def complexDualRealIsometry (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    StrongDual ℂ E ≃ₗᵢ[ℝ] StrongDual ℝ E :=
  (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm

theorem not_hasComplexUnconditionalSchauderBasis_dual_of_real_equiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (hF : chiDPR (StrongDual ℝ F) = ⊤) :
    ¬ HasUnconditionalSchauderBasis ℂ (StrongDual ℂ E) := by
  let ed : StrongDual ℂ E ≃L[ℝ] StrongDual ℝ F :=
    (complexDualRealIsometry E).toContinuousLinearEquiv.trans
      (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  exact not_hasComplexUnconditionalSchauderBasis_of_real_equiv ed hF

end ComplementedSubspace
