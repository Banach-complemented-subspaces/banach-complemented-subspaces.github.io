import ComplementedSubspace.LocalHilbert
import ComplementedSubspace.HilbertComplement

/-!
Transfer of the elementary Hilbert projection-complement estimate through the
Hilbert norms constructed by the qualitative compactness argument.
-/

noncomputable section

namespace ComplementedSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero idempotent has norm at least one in any real normed space. -/
theorem norm_nonzero_idempotent_ge_one (P : E →L[ℝ] E)
    (hPP : P.comp P = P) (hP : P ≠ 0) : 1 ≤ ‖P‖ := by
  obtain ⟨x, hx⟩ : ∃ x : E, P x ≠ 0 := by
    by_contra! h
    exact hP (ContinuousLinearMap.ext h)
  have hfix : P (P x) = P x := by
    simpa only [ContinuousLinearMap.comp_apply] using congrArg (fun T => T x) hPP
  have h := P.le_opNorm (P x)
  rw [hfix] at h
  exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hx)).mp (by simpa only [mul_comm, one_mul, mul_one] using h)

/-- An equivalent Hilbert norm with distortion `D` gives the complement bound
`D² * ||P||`; no completeness or finite-dimensionality is needed for this
transfer. -/
theorem HasHilbertNormWithin.norm_complement_le {D : ℝ} (hD : 0 ≤ D)
    (h : HasHilbertNormWithin E D) (P : E →L[ℝ] E)
    (hPP : P.comp P = P) (hP : P ≠ 0) :
    ‖ContinuousLinearMap.id ℝ E - P‖ ≤ D ^ 2 * ‖P‖ := by
  obtain ⟨p, hp⟩ := h.exists_model
  let Q₀ : p.Space →ₗ[ℝ] p.Space := P.toLinearMap
  have hboundOriginal (x : E) : p.q (P x) ≤ (D * ‖P‖) * p.q x := by
    calc
      p.q (P x) ≤ ‖P x‖ := (hp (P x)).1
      _ ≤ ‖P‖ * ‖(x : E)‖ := P.le_opNorm x
      _ ≤ ‖P‖ * (D * p.q x) := mul_le_mul_of_nonneg_left (hp x).2 (norm_nonneg _)
      _ = (D * ‖P‖) * p.q x := by ring
  have hQbound (x : p.Space) : ‖Q₀ x‖ ≤ (D * ‖P‖) * ‖x‖ := hboundOriginal x
  let Q : p.Space →L[ℝ] p.Space := Q₀.mkContinuous (D * ‖P‖) hQbound
  have hQQ : Q.comp Q = Q := by
    ext x
    exact congrArg (fun T : E →L[ℝ] E => T x) hPP
  have hQne : Q ≠ 0 := by
    intro hz
    apply hP
    ext x
    exact congrArg (fun T : p.Space →L[ℝ] p.Space => T x) hz
  have hnQ : ‖Q‖ ≤ D * ‖P‖ :=
    Q.opNorm_le_bound (mul_nonneg hD (norm_nonneg _)) hQbound
  have hnQc := (hilbert_norm_complement_le Q hQQ hQne).trans hnQ
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  intro x
  change ‖x - P x‖ ≤ (D ^ 2 * ‖P‖) * ‖x‖
  have hpoint : p.q (x - P x) ≤ (D * ‖P‖) * p.q x := by
    have hv := (ContinuousLinearMap.id ℝ p.Space - Q).le_opNorm (show p.Space from x)
    exact hv.trans (mul_le_mul_of_nonneg_right hnQc (apply_nonneg p.q x))
  calc
    ‖x - P x‖ ≤ D * p.q (x - P x) := (hp _).2
    _ ≤ D * ((D * ‖P‖) * p.q x) := mul_le_mul_of_nonneg_left hpoint hD
    _ ≤ D * ((D * ‖P‖) * ‖x‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hp x).1 (mul_nonneg hD (norm_nonneg _))) hD
    _ = (D ^ 2 * ‖P‖) * ‖x‖ := by ring

/-- Only the two-dimensional local geometry is needed for the complementary
projection estimate. The invariant subspace used at `x` is `span{x,Px}`. -/
theorem norm_complement_le_of_localHilbert {D : ℝ} (hD : 1 ≤ D)
    (hlocal : ∀ (S : Submodule ℝ E) [FiniteDimensional ℝ S],
      Module.finrank ℝ S ≤ 2 → HasHilbertNormWithin S D)
    (P : E →L[ℝ] E) (hPP : P.comp P = P) (hP : P ≠ 0) :
    ‖ContinuousLinearMap.id ℝ E - P‖ ≤ D ^ 2 * ‖P‖ := by
  classical
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hP1 := norm_nonzero_idempotent_ge_one P hPP hP
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  intro x
  let s : Finset E := {x, P x}
  let S : Submodule ℝ E := Submodule.span ℝ (s : Set E)
  have hSfg : S.FG := ⟨s, rfl⟩
  letI : FiniteDimensional ℝ S := .of_fg hSfg
  have hdim : Module.finrank ℝ S ≤ 2 := by
    apply (finrank_span_finset_le_card s).trans
    simpa only [s, Finset.card_singleton] using Finset.card_insert_le x ({P x} : Finset E)
  have hx : x ∈ S := Submodule.subset_span (by simp [s])
  have hPx : P x ∈ S := Submodule.subset_span (by simp [s])
  have hstable : ∀ z ∈ S, P z ∈ S := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        have hcases : z = x ∨ z = P x := by simpa [s] using hz
        rcases hcases with rfl | rfl
        · exact hPx
        · have hh : P (P x) = P x := congrArg (fun T : E →L[ℝ] E => T x) hPP
          simpa only [hh] using hPx
    | zero => simpa only [map_zero] using S.zero_mem
    | add z w hz hw hPz hPw => simpa only [map_add] using S.add_mem hPz hPw
    | smul r z hz hPz => simpa only [map_smul] using S.smul_mem r hPz
  let R₀ : S →ₗ[ℝ] S := P.toLinearMap.restrict hstable
  let R : S →L[ℝ] S := R₀.mkContinuous ‖P‖ (fun z => P.le_opNorm z)
  have hRR : R.comp R = R := by
    ext z
    exact congrArg (fun T : E →L[ℝ] E => T z) hPP
  by_cases hR : R = 0
  · have hPx0 : P x = 0 := by
      have hh := congrArg (fun T : S →L[ℝ] S => (T ⟨x, hx⟩ : E)) hR
      exact hh
    change ‖x - P x‖ ≤ (D ^ 2 * ‖P‖) * ‖x‖
    rw [hPx0, sub_zero]
    have hD1 : 1 ≤ D ^ 2 := by nlinarith
    have hp : 1 ≤ D ^ 2 * ‖P‖ :=
      hD1.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hP1 (sq_nonneg D))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg x)
  · have hnR : ‖R‖ ≤ ‖P‖ := R.opNorm_le_bound (norm_nonneg _) (fun z => P.le_opNorm z)
    have hbound := ((hlocal S hdim).norm_complement_le hD0 R hRR hR).trans
      (mul_le_mul_of_nonneg_left hnR (sq_nonneg D))
    have hv := (ContinuousLinearMap.id ℝ S - R).le_opNorm ⟨x, hx⟩
    exact hv.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))

/-- A dimension-independent complement estimate follows from a sufficiently
small ambient parallelogram defect. -/
theorem exists_parallelogram_complement_threshold {D : ℝ} (hD : 1 < D) :
    ∃ ν > 1, ∀ (P : E →L[ℝ] E),
      ApproxParallelogram (fun x : E => ‖x‖) ν → P.comp P = P → P ≠ 0 →
      ‖ContinuousLinearMap.id ℝ E - P‖ ≤ D ^ 2 * ‖P‖ := by
  obtain ⟨ν, hν, hlocal⟩ := exists_localHilbert_subspace_threshold 2 hD
  refine ⟨ν, hν, ?_⟩
  intro P hpar hPP hP
  exact norm_complement_le_of_localHilbert hD.le (hlocal E hpar) P hPP hP

end ComplementedSubspace
