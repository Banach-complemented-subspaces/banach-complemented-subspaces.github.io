import ComplementedSubspace.ProductFrameTraceBound
import ComplementedSubspace.FiniteParameterBounds

/-!
# Scalar simplification of the finite overlap estimate

The witness g at the conjugate exponent and the uniform Hilbert bound H are
kept distinct. All powers of the unconditional constant are combined exactly
before bounding their total exponent by three.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ComplementedSubspace

def realFrameOverlapPenalty (n : ℕ) (p : ℝ) : ℝ :=
  (5 / 4 : ℝ) ^ ((n : ℝ) * (p - 2) / (2 * p)) *
    realFrameHilbertScale n p ^ (4 * (p - 2) / p)

theorem realFrameOverlapPenalty_pos (n : ℕ) (p : ℝ) :
    0 < realFrameOverlapPenalty n p := by
  unfold realFrameOverlapPenalty realFrameHilbertScale
  positivity

theorem realFrameOverlapPenalty_compensation (n : ℕ) {p : ℝ} (hp : p ≠ 0) :
    realFrameWitnessScale n (frameConjugate p) * realFrameOverlapPenalty n p =
      (realFrameOverlapScale n p)⁻¹ := by
  unfold realFrameOverlapPenalty realFrameWitnessScale realFrameHilbertScale realFrameOverlapScale
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5 / 4),
    ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_neg]
  congr 1
  unfold realFrameLogOverlap
  field_simp
  <;> ring

theorem realFrameHilbertScale_ge_one (n : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    1 ≤ realFrameHilbertScale n p := by
  rw [realFrameHilbertScale_eq]
  apply Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
  apply mul_nonneg (Nat.cast_nonneg _)
  have hp0 : 0 < p := by linarith
  have hi : 1 / p ≤ 1 / 2 := (div_le_div_iff₀ hp0 (by norm_num)).2 (by linarith)
  linarith

theorem realFrameOverlapPenalty_ge_one (n : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    1 ≤ realFrameOverlapPenalty n p := by
  have hp0 : 0 < p := by linarith
  unfold realFrameOverlapPenalty
  have h₁ := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 5 / 4)
    (by positivity : 0 ≤ (n : ℝ) * (p - 2) / (2 * p))
  have h₂ := Real.one_le_rpow (realFrameHilbertScale_ge_one n hp)
    (by positivity : 0 ≤ 4 * (p - 2) / p)
  simpa only [one_mul] using mul_le_mul h₁ h₂ (by norm_num : (0 : ℝ) ≤ 1)
    (zero_le_one.trans h₁)

private theorem overlap_scalar_bounds {p : ℝ} (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3) :
    0 ≤ realFrameSignConstant p ∧ realFrameSignConstant p ≤ 2 ∧
      0 ≤ (3 : ℝ) ^ ((p - 2) / p) + 1 ∧
      (3 : ℝ) ^ ((p - 2) / p) + 1 ≤ 4 ∧
      Real.sqrt ((3 : ℝ) ^ ((p - 2) / p) + 1) ≤ 2 := by
  have hp : 0 < p := by linarith
  have he : (p - 2) / p ≤ 1 := (div_le_one hp).2 (by linarith)
  have hm : (3 : ℝ) ^ ((p - 2) / p) ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) he
  have hm0 : 0 ≤ (3 : ℝ) ^ ((p - 2) / p) + 1 := by positivity
  have hb0 : 0 ≤ realFrameSignConstant p := Real.rpow_nonneg (by norm_num) _
  have hb : realFrameSignConstant p ≤ 2 := by
    have hs := realFrameSignConstant_sq p
    nlinarith
  have hs : Real.sqrt ((3 : ℝ) ^ ((p - 2) / p) + 1) ≤ 2 := by
    exact Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  exact ⟨hb0, hb, hm0, by linarith, hs⟩

/-- Scalar form matching the finite unconditional overlap estimate. -/
theorem finite_overlap_scale_bound (n : ℕ) (p : ℝ) (m : ℕ) (C : ℝ)
    (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3) (hC : 1 ≤ C)
    (hm : (m : ℝ) ≤ 3 * (2 : ℝ) ^ n) :
    realFrameWitnessScale n (frameConjugate p) *
      (C * (realFrameSignConstant p *
        ((C ^ 2 * ((3 : ℝ) ^ ((p - 2) / p) + 1)) ^ ((4 - p) / (2 * p)) *
          ((m : ℝ) * (C * realFrameHilbertScale n p) ^ 8 * (5 / 8 : ℝ) ^ n) ^
            ((p - 2) / (2 * p))) +
        C * Real.sqrt ((3 : ℝ) ^ ((p - 2) / p) + 1))) ≤
      64 * C ^ 3 / realFrameOverlapScale n p := by
  have hp : 0 < p := by linarith
  have hCp : 0 < C := by linarith
  let a : ℝ := (4 - p) / (2 * p)
  let b : ℝ := (p - 2) / (2 * p)
  let M : ℝ := (3 : ℝ) ^ ((p - 2) / p) + 1
  let H : ℝ := realFrameHilbertScale n p
  let T : ℝ := realFrameOverlapPenalty n p
  have ha0 : 0 ≤ a := by dsimp [a]; exact div_nonneg (by linarith) (by positivity)
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; apply (div_le_one (by positivity)).2; linarith
  have hb1 : b ≤ 1 := by dsimp [b]; apply (div_le_one (by positivity)).2; linarith
  have hH : 0 < H := Real.exp_pos _
  have hT : 1 ≤ T := realFrameOverlapPenalty_ge_one n hp₂
  obtain ⟨hβ0, hβ, hM0, hM, hsqrt⟩ := overlap_scalar_bounds hp₂ hp₃
  have hMa : M ^ a ≤ 4 := by
    calc
      M ^ a ≤ (4 : ℝ) ^ a := Real.rpow_le_rpow hM0 hM ha0
      _ ≤ 4 := by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) ha1
  have h3b : (3 : ℝ) ^ b ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hb1
  have hpow : 1 + 2 * a + 8 * b ≤ 3 := by
    dsimp [a, b]
    field_simp
    nlinarith
  have hCpow : C ^ (1 + 2 * a + 8 * b) ≤ C ^ 3 := by
    exact (Real.rpow_le_rpow_of_exponent_le hC hpow).trans_eq (Real.rpow_natCast C 3)
  have hB : (m : ℝ) * (C * H) ^ 8 * (5 / 8 : ℝ) ^ n ≤
      3 * (C * H) ^ 8 * (5 / 4 : ℝ) ^ n := by
    calc
      _ ≤ (3 * (2 : ℝ) ^ n) * (C * H) ^ 8 * (5 / 8 : ℝ) ^ n := by gcongr
      _ = 3 * (C * H) ^ 8 * ((2 : ℝ) * (5 / 8 : ℝ)) ^ n := by
        rw [mul_pow (2 : ℝ) (5 / 8 : ℝ) n]
        ring
      _ = _ := by norm_num
  have hid : C * (realFrameSignConstant p *
      ((C ^ 2 * M) ^ a * (3 * (C * H) ^ 8 * (5 / 4 : ℝ) ^ n) ^ b)) =
        realFrameSignConstant p * M ^ a * (3 : ℝ) ^ b *
          C ^ (1 + 2 * a + 8 * b) * T := by
    rw [Real.mul_rpow (sq_nonneg C) (show 0 ≤ M from hM0)]
    simp only [
      Real.mul_rpow (by positivity : 0 ≤ 3 * (C * H) ^ 8) (by positivity : 0 ≤ (5 / 4 : ℝ) ^ n),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity : 0 ≤ (C * H) ^ 8),
      ← Real.rpow_natCast_mul hCp.le, ← Real.rpow_natCast_mul (mul_pos hCp hH).le,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 5 / 4),
      Real.mul_rpow hCp.le hH.le]
    have heC : C ^ (1 + 2 * a + 8 * b) = C * C ^ (2 * a) * C ^ (8 * b) := by
      rw [Real.rpow_add hCp, Real.rpow_add hCp, Real.rpow_one]
    have heT : T = (5 / 4 : ℝ) ^ ((n : ℝ) * b) * H ^ (8 * b) := by
      dsimp [T, realFrameOverlapPenalty, H, b]
      congr 2 <;> field_simp <;> ring
    rw [heC, heT]
    ring
  have hfirst : C * (realFrameSignConstant p *
      ((C ^ 2 * M) ^ a * ((m : ℝ) * (C * H) ^ 8 * (5 / 8 : ℝ) ^ n) ^ b)) ≤
      24 * C ^ 3 * T := by
    calc
      _ ≤ C * (realFrameSignConstant p *
          ((C ^ 2 * M) ^ a * (3 * (C * H) ^ 8 * (5 / 4 : ℝ) ^ n) ^ b)) := by
        gcongr
      _ = _ := hid
      _ ≤ 2 * 4 * 3 * C ^ 3 * T := by gcongr
      _ = _ := by ring
  have hsecond : C * (C * Real.sqrt M) ≤ 2 * C ^ 3 * T := by
    have hCC : C ^ 2 ≤ C ^ 3 := pow_le_pow_right₀ hC (by decide : 2 ≤ 3)
    calc
      C * (C * Real.sqrt M) = C ^ 2 * Real.sqrt M := by ring
      _ ≤ C ^ 3 * 2 := by gcongr
      _ ≤ C ^ 3 * 2 * T := le_mul_of_one_le_right (by positivity) hT
      _ = _ := by ring
  have hsum : C * (realFrameSignConstant p *
      ((C ^ 2 * M) ^ a * ((m : ℝ) * (C * H) ^ 8 * (5 / 8 : ℝ) ^ n) ^ b) +
        C * Real.sqrt M) ≤ 26 * C ^ 3 * T := by nlinarith
  have hg : 0 ≤ realFrameWitnessScale n (frameConjugate p) := (Real.exp_pos _).le
  have hL : 0 < realFrameOverlapScale n p := Real.exp_pos _
  calc
    _ ≤ realFrameWitnessScale n (frameConjugate p) * (26 * C ^ 3 * T) :=
      mul_le_mul_of_nonneg_left hsum hg
    _ = 26 * C ^ 3 / realFrameOverlapScale n p := by
      rw [show realFrameWitnessScale n (frameConjugate p) * (26 * C ^ 3 * T) =
        26 * C ^ 3 * (realFrameWitnessScale n (frameConjugate p) * T) by ring]
      rw [realFrameOverlapPenalty_compensation n hp.ne']
      rfl
    _ ≤ _ := by gcongr <;> norm_num

/-! A coarse separation condition is enough for the selection contradiction. -/

theorem finite_overlap_separation_lt_half {D K L : ℝ}
    (hD : 2 ≤ D) (hK : 0 ≤ K) (hDK : 8 * K ≤ D) (hL : D ^ 8 < L) :
    64 * (D * K) ^ 3 / L < 1 / 2 := by
  have hD0 : 0 ≤ D := by linarith
  have hL0 : 0 < L := lt_of_le_of_lt (pow_nonneg hD0 _) hL
  have hKpow := pow_le_pow_left₀ (by positivity : 0 ≤ 8 * K) hDK 3
  have hmul := mul_le_mul_of_nonneg_left hKpow (pow_nonneg hD0 3)
  have hpows : D ^ 6 ≤ D ^ 8 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ D) (by decide : 6 ≤ 8)
  have hnum : 64 * (D * K) ^ 3 ≤ D ^ 8 / 8 := by nlinarith
  apply (div_lt_iff₀ hL0).2
  nlinarith

theorem finite_overlap_selection_contradiction {θ D K L : ℝ}
    (hθ : 1 / 2 ≤ θ) (hupper : θ ≤ 64 * (D * K) ^ 3 / L)
    (hD : 2 ≤ D) (hK : 0 ≤ K) (hDK : 8 * K ≤ D) (hL : D ^ 8 < L) : False := by
  exact (not_lt_of_ge (hθ.trans hupper)) (finite_overlap_separation_lt_half hD hK hDK hL)

/-- The trace-to-overlap passage loses the factor `4 K² beta²`; its actual
weighted lower bound still contradicts the overlap upper estimate. -/
theorem finite_overlap_weighted_separation_lt_one {D K L β : ℝ}
    (hD : 2 ≤ D) (hK : 0 ≤ K) (hDK : 8 * K ≤ D) (hL : D ^ 8 < L)
    (hβ : β ^ 2 ≤ 4) :
    4 * K ^ 2 * β ^ 2 * (64 * (D * K) ^ 3 / L) < 1 := by
  have hD0 : 0 ≤ D := by linarith
  have hL0 : 0 < L := lt_of_le_of_lt (pow_nonneg hD0 _) hL
  have hKpow := pow_le_pow_left₀ (by positivity : 0 ≤ 8 * K) hDK 5
  have hmul := mul_le_mul_of_nonneg_left hKpow (pow_nonneg hD0 3)
  have hβmul := mul_le_mul_of_nonneg_left hβ
    (by positivity : 0 ≤ 256 * K ^ 2 * (D * K) ^ 3)
  have hnum : 4 * K ^ 2 * β ^ 2 * (64 * (D * K) ^ 3) ≤ D ^ 8 / 32 := by
    nlinarith
  rw [show 4 * K ^ 2 * β ^ 2 * (64 * (D * K) ^ 3 / L) =
    (4 * K ^ 2 * β ^ 2 * (64 * (D * K) ^ 3)) / L by ring]
  apply (div_lt_one hL0).2
  nlinarith

theorem finite_overlap_weighted_selection_contradiction {θ D K L β : ℝ}
    (hlower : 1 ≤ 4 * K ^ 2 * β ^ 2 * θ)
    (hupper : θ ≤ 64 * (D * K) ^ 3 / L)
    (hD : 2 ≤ D) (hK : 0 ≤ K) (hDK : 8 * K ≤ D) (hL : D ^ 8 < L)
    (hβ : β ^ 2 ≤ 4) : False := by
  have h := mul_le_mul_of_nonneg_left hupper
    (by positivity : 0 ≤ 4 * K ^ 2 * β ^ 2)
  exact (not_lt_of_ge (hlower.trans h))
    (finite_overlap_weighted_separation_lt_one hD hK hDK hL hβ)

theorem realFrameSignConstant_sq_le_four {p : ℝ} (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3) :
    realFrameSignConstant p ^ 2 ≤ 4 := by
  obtain ⟨hβ0, hβ, _⟩ := overlap_scalar_bounds hp₂ hp₃
  nlinarith

theorem finite_overlap_trace_separation {D K L β : ℝ}
    (hD : 2 ≤ D) (hK : 0 ≤ K) (hDK : 8 * K ≤ D) (hL : D ^ 8 < L)
    (hβ : β ^ 2 ≤ 4) : 256 * K ^ 2 * β ^ 2 * (D * K) ^ 3 < L := by
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity : 0 ≤ D ^ 8) hL
  have h := finite_overlap_weighted_separation_lt_one hD hK hDK hL hβ
  have he : 4 * K ^ 2 * β ^ 2 * (64 * (D * K) ^ 3 / L) =
      (256 * K ^ 2 * β ^ 2 * (D * K) ^ 3) / L := by ring
  rw [he] at h
  exact (div_lt_one hL0).mp h

theorem finite_selection_smallness {q β D K g : ℝ} (hq : 0 ≤ q)
    (hβ : β ≤ 2) (hD : 2 ≤ D) (hK : 0 ≤ K) (hDK : 8 * K ≤ D)
    (hg : D ^ 8 < g) : (q * β / g) * D * K ^ 2 ≤ q / 4 := by
  have hD0 : 0 ≤ D := by linarith
  have hg0 : 0 < g := lt_of_le_of_lt (pow_nonneg hD0 _) hg
  have hKpow := pow_le_pow_left₀ (by positivity : 0 ≤ 8 * K) hDK 2
  have hmul := mul_le_mul_of_nonneg_left hKpow hD0
  have hβmul := mul_le_mul_of_nonneg_right hβ (by positivity : 0 ≤ D * K ^ 2)
  have hpows : D ^ 3 ≤ D ^ 8 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ D) (by decide : 3 ≤ 8)
  have hbase : β * D * K ^ 2 ≤ g / 4 := by nlinarith
  rw [show (q * β / g) * D * K ^ 2 = (q * (β * D * K ^ 2)) / g by ring]
  apply (div_le_iff₀ hg0).2
  have hh := mul_le_mul_of_nonneg_left hbase hq
  nlinarith

theorem finite_frame_selection_scalar_bounds (n : ℕ) (p D K : ℝ)
    (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3) (hD : 2 ≤ D) (hK : 0 ≤ K)
    (hDK : 8 * K ≤ D) (hL : D ^ 8 < realFrameOverlapScale n p) :
    (((2 : ℝ) ^ n * realFrameSignConstant p / realFrameWitnessScale n p) * D * K ^ 2 ≤
      (2 : ℝ) ^ n / 4) ∧
    256 * K ^ 2 * realFrameSignConstant p ^ 2 * (D * K) ^ 3 <
      realFrameOverlapScale n p := by
  obtain ⟨hβ0, hβ, _⟩ := overlap_scalar_bounds hp₂ hp₃
  exact ⟨finite_selection_smallness (by positivity) hβ hD hK hDK
    (hL.trans_le (realFrameOverlapScale_le_witnessScale n hp₂)),
    finite_overlap_trace_separation hD hK hDK hL
      (realFrameSignConstant_sq_le_four hp₂ hp₃)⟩

end ComplementedSubspace
