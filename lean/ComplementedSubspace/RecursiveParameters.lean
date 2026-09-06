import ComplementedSubspace.FiniteParameterBounds
import ComplementedSubspace.FiniteLpGeometry
import ComplementedSubspace.LocalHilbert
import ComplementedSubspace.Ambient

/-!
# Recursive finite-frame block parameters

Each stage meets finitely many restrictions from earlier blocks. We use the
full ambient Hilbert bound `(4^n)^(1/2-1/p)` when separating heads from tails.
The explicit one-parameter family is only used to prove each choice exists;
the resulting sequence retains its actual integer orders and real exponents.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Topology

namespace ComplementedSubspace

/-- One admissible finite-frame block. -/
structure FiniteFrameChoice where
  order : ℕ
  exponent : ℝ
  order_pos : 0 < order
  two_lt_exponent : 2 < exponent
  exponent_le_three : exponent ≤ 3

namespace FiniteFrameChoice

def epsilon (c : FiniteFrameChoice) : ℝ := c.exponent - 2

theorem epsilon_pos (c : FiniteFrameChoice) : 0 < c.epsilon :=
  sub_pos.2 c.two_lt_exponent

/-- Full ambient comparison, necessary for both complementary ranges. -/
def ambientHilbertBound (c : FiniteFrameChoice) : ℝ :=
  ((4 : ℝ) ^ c.order) ^ (1 / 2 - 1 / c.exponent)

theorem ambientHilbertBound_pos (c : FiniteFrameChoice) : 0 < c.ambientHilbertBound := by
  unfold ambientHilbertBound
  positivity

end FiniteFrameChoice

private def historyHilbertBound : List FiniteFrameChoice → ℝ
  | [] => 2
  | c :: cs => max c.ambientHilbertBound (historyHilbertBound cs)

private theorem historyHilbertBound_ge_two (cs : List FiniteFrameChoice) :
    2 ≤ historyHilbertBound cs := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih => exact ih.trans (le_max_right _ _)

private theorem historyHilbertBound_ge_mem {cs : List FiniteFrameChoice}
    {c : FiniteFrameChoice} (hc : c ∈ cs) : c.ambientHilbertBound ≤ historyHilbertBound cs := by
  induction cs with
  | nil => simp at hc
  | cons b cs ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact le_max_left _ _
    · exact (ih hc).trans (le_max_right _ _)

/-- A slightly enlarged head bound also guarantees unbounded separation. -/
private def stageHeadBound (cs : List FiniteFrameChoice) : ℝ :=
  historyHilbertBound cs + cs.length

private def historyTolerance (η : ℝ) (θ : ℕ → ℝ) : List FiniteFrameChoice → ℝ
  | [] => η
  | c :: cs => min (min c.epsilon (θ c.order)) (historyTolerance η θ cs)

private theorem historyTolerance_pos {η : ℝ} (hη : 0 < η)
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 < θ n) (cs : List FiniteFrameChoice) :
    0 < historyTolerance η θ cs := by
  induction cs with
  | nil => exact hη
  | cons c cs ih => exact lt_min (lt_min c.epsilon_pos (hθ c.order)) ih

private theorem historyTolerance_le_error (η : ℝ) (θ : ℕ → ℝ)
    (cs : List FiniteFrameChoice) : historyTolerance η θ cs ≤ η := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih => exact (min_le_right _ _).trans ih

private theorem historyTolerance_le_mem (η : ℝ) (θ : ℕ → ℝ)
    {cs : List FiniteFrameChoice} {c : FiniteFrameChoice} (hc : c ∈ cs) :
    historyTolerance η θ cs ≤ c.epsilon ∧ historyTolerance η θ cs ≤ θ c.order := by
  induction cs with
  | nil => simp at hc
  | cons b cs ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨(min_le_left _ _).trans (min_le_left _ _),
        (min_le_left _ _).trans (min_le_right _ _)⟩
    · obtain ⟨h₁, h₂⟩ := ih hc
      exact ⟨(min_le_right _ _).trans h₁, (min_le_right _ _).trans h₂⟩

private def NextFrameChoiceSpec (η : ℝ) (θ : ℕ → ℝ)
    (cs : List FiniteFrameChoice) (c : FiniteFrameChoice) : Prop :=
  (c.order : ℝ) * c.epsilon ^ 2 < η ∧
  c.epsilon < 1 / ((cs.length : ℝ) + 1) ∧
  stageHeadBound cs ^ 8 < realFrameOverlapScale c.order c.exponent ∧
  ∀ b ∈ cs, c.exponent < b.exponent ∧ c.epsilon < θ b.order

private theorem exists_nextFrameChoice {η : ℝ} (hη : 0 < η)
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 < θ n) (cs : List FiniteFrameChoice) :
    ∃ c, NextFrameChoiceSpec η θ cs c := by
  let δ : ℝ := min (1 / ((cs.length : ℝ) + 1)) (historyTolerance η θ cs)
  have hδ : 0 < δ := lt_min (by positivity) (historyTolerance_pos hη hθ cs)
  obtain ⟨n, p, hn, hp, hp₃, he, hquad, hL⟩ :=
    exists_finiteFrame_parameters hδ (stageHeadBound cs ^ 8)
  let c : FiniteFrameChoice := ⟨n, p, hn, hp, hp₃⟩
  refine ⟨c, ?_, ?_, hL, ?_⟩
  · exact hquad.trans_le ((min_le_right _ _).trans (historyTolerance_le_error η θ cs))
  · exact he.trans_le (min_le_left _ _)
  · intro b hb
    have hm := historyTolerance_le_mem η θ hb
    have hbε : p - 2 < b.epsilon :=
      he.trans_le ((min_le_right _ _).trans hm.1)
    refine ⟨?_, he.trans_le ((min_le_right _ _).trans hm.2)⟩
    change p < b.exponent
    unfold FiniteFrameChoice.epsilon at hbε
    linarith

private def nextFrameChoice {η : ℝ} (hη : 0 < η)
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 < θ n) (cs : List FiniteFrameChoice) : FiniteFrameChoice :=
  Classical.choose (exists_nextFrameChoice hη hθ cs)

private theorem nextFrameChoice_spec {η : ℝ} (hη : 0 < η)
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 < θ n) (cs : List FiniteFrameChoice) :
    NextFrameChoiceSpec η θ cs (nextFrameChoice hη hθ cs) :=
  Classical.choose_spec (exists_nextFrameChoice hη hθ cs)

private def frameChoiceHistory {η : ℝ} (hη : 0 < η)
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 < θ n) : ℕ → List FiniteFrameChoice
  | 0 => []
  | k + 1 => nextFrameChoice hη hθ (frameChoiceHistory hη hθ k) ::
      frameChoiceHistory hη hθ k

private def selectedFrameChoice {η : ℝ} (hη : 0 < η)
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 < θ n) (k : ℕ) : FiniteFrameChoice :=
  nextFrameChoice hη hθ (frameChoiceHistory hη hθ k)

private theorem frameChoiceHistory_length {η : ℝ} (hη : 0 < η)
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 < θ n) (k : ℕ) :
    (frameChoiceHistory hη hθ k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [frameChoiceHistory, List.length_cons, ih]

private theorem selectedFrameChoice_mem_history {η : ℝ} (hη : 0 < η)
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 < θ n) {i j : ℕ} (hij : i < j) :
    selectedFrameChoice hη hθ i ∈ frameChoiceHistory hη hθ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases he : i = j
    · subst i
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by omega))

/-- All information needed from the recursive simultaneous choice. -/
structure RecursiveFrameSelection (η : ℝ) (θ : ℕ → ℝ) where
  block : ℕ → FiniteFrameChoice
  headBound : ℕ → ℝ
  exponent_strictAnti : StrictAnti (fun j => (block j).exponent)
  exponent_tendsto : Tendsto (fun j => (block j).exponent) atTop (𝓝 2)
  quadratic_error : ∀ j, ((block j).order : ℝ) * (block j).epsilon ^ 2 < η
  headBound_ge_index : ∀ j : ℕ, (j : ℝ) + 2 ≤ headBound j
  earlier_ambient_bound : ∀ i j, i < j → (block i).ambientHilbertBound ≤ headBound j
  overlap_separation : ∀ j, headBound j ^ 8 <
    realFrameOverlapScale (block j).order (block j).exponent
  later_exponent_small : ∀ i j, i < j → (block j).epsilon < θ (block i).order

/-- Finite-history recursion with an arbitrary positive geometry tolerance
depending on each earlier tensor order. -/
theorem exists_recursiveFrameSelection {η : ℝ} (hη : 0 < η)
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 < θ n) : Nonempty (RecursiveFrameSelection η θ) := by
  let c := selectedFrameChoice hη hθ
  let D := fun j => stageHeadBound (frameChoiceHistory hη hθ j)
  have hs (j : ℕ) : NextFrameChoiceSpec η θ (frameChoiceHistory hη hθ j) (c j) :=
    nextFrameChoice_spec hη hθ _
  have he (j : ℕ) : (c j).epsilon < 1 / ((j : ℝ) + 1) := by
    simpa only [frameChoiceHistory_length] using (hs j).2.1
  have hεlim : Tendsto (fun j => (c j).epsilon) atTop (𝓝 0) :=
    squeeze_zero (fun j => (c j).epsilon_pos.le) (fun j => (he j).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨⟨c, D, ?_, ?_, fun j => (hs j).1, ?_, ?_,
    fun j => (hs j).2.2.1, ?_⟩⟩
  · intro i j hij
    exact ((hs j).2.2.2 (c i) (selectedFrameChoice_mem_history hη hθ hij)).1
  · have h := (tendsto_const_nhds (x := (2 : ℝ))).add hεlim
    convert! h using 1
    · ext j
      simp [FiniteFrameChoice.epsilon]
    · norm_num
  · intro j
    have h := historyHilbertBound_ge_two (frameChoiceHistory hη hθ j)
    change (j : ℝ) + 2 ≤ historyHilbertBound (frameChoiceHistory hη hθ j) +
      (frameChoiceHistory hη hθ j).length
    rw [frameChoiceHistory_length]
    linarith
  · intro i j hij
    have h := historyHilbertBound_ge_mem (selectedFrameChoice_mem_history hη hθ hij)
    exact h.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  · intro i j hij
    exact ((hs j).2.2.2 (c i) (selectedFrameChoice_mem_history hη hθ hij)).2

namespace RecursiveFrameSelection

variable {η : ℝ} {θ : ℕ → ℝ} (s : RecursiveFrameSelection η θ)

theorem headBound_ge_two (j : ℕ) : 2 ≤ s.headBound j := by
  have h := s.headBound_ge_index j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem overlap_ge_index (j : ℕ) :
    (j : ℝ) + 2 ≤ realFrameOverlapScale (s.block j).order (s.block j).exponent := by
  have hD : 1 ≤ s.headBound j := (by norm_num : (1 : ℝ) ≤ 2).trans (s.headBound_ge_two j)
  exact (s.headBound_ge_index j).trans
    ((le_self_pow₀ hD (by decide : (8 : ℕ) ≠ 0)).trans (s.overlap_separation j).le)

theorem overlap_tendsto :
    Tendsto (fun j => realFrameOverlapScale (s.block j).order (s.block j).exponent)
      atTop atTop := by
  apply tendsto_atTop_mono s.overlap_ge_index
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

/-- The recursive choices as the actual parameters of the ambient lp2 sum. -/
def toBlockParameters : BlockParameters where
  dimension j := ⟨4 ^ (s.block j).order, by positivity⟩
  exponent j := (s.block j).exponent
  two_lt_exponent j := (s.block j).two_lt_exponent
  exponent_le_three j := (s.block j).exponent_le_three
  exponent_antitone := s.exponent_strictAnti.antitone
  exponent_tendsto := s.exponent_tendsto

@[simp] theorem toBlockParameters_dimension (j : ℕ) :
    ((s.toBlockParameters.dimension j : ℕ)) = 4 ^ (s.block j).order := rfl

@[simp] theorem toBlockParameters_exponent (j : ℕ) :
    s.toBlockParameters.exponent j = (s.block j).exponent := rfl

end RecursiveFrameSelection

/-- A selected threshold for real local Hilbert approximation with distortion two. -/
def recursiveLocalHilbertThreshold (d : ℕ) : ℝ :=
  Classical.choose (exists_localHilbert_subspace_threshold.{0} d (D := 2) (by norm_num))

theorem recursiveLocalHilbertThreshold_gt_one (d : ℕ) :
    1 < recursiveLocalHilbertThreshold d :=
  (Classical.choose_spec
    (exists_localHilbert_subspace_threshold.{0} d (D := 2) (by norm_num))).1

theorem recursiveLocalHilbertThreshold_spec (d : ℕ)
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hpar : ApproxParallelogram (fun x : F => ‖x‖) (recursiveLocalHilbertThreshold d))
    (S : Submodule ℝ F) [FiniteDimensional ℝ S] (hS : Module.finrank ℝ S ≤ d) :
    HasHilbertNormWithin S 2 :=
  (Classical.choose_spec
    (exists_localHilbert_subspace_threshold.{0} d (D := 2) (by norm_num))).2 F hpar S hS

theorem exists_frameExponent_tolerance {ν : ℝ} (hν : 1 < ν) :
    ∃ δ > 0, ∀ p : ℝ, 2 ≤ p → p - 2 < δ → (2 : ℝ) ^ (2 - 4 / p) < ν := by
  have h := finitePiLp_parallelogram_constant_tendsto.eventually (gt_mem_nhds hν)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨δ, hδ, ?_⟩
  intro p hp hpδ
  apply hball
  simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hp)] using hpδ

/-- Tolerance imposed by an earlier block of tensor order n and dimension 2^n. -/
def recursiveFrameExponentTolerance (n : ℕ) : ℝ :=
  Classical.choose (exists_frameExponent_tolerance
    (recursiveLocalHilbertThreshold_gt_one (3 * 2 ^ n)))

theorem recursiveFrameExponentTolerance_pos (n : ℕ) :
    0 < recursiveFrameExponentTolerance n :=
  (Classical.choose_spec (exists_frameExponent_tolerance
    (recursiveLocalHilbertThreshold_gt_one (3 * 2 ^ n)))).1

theorem recursiveFrameExponentTolerance_spec (n : ℕ) {p : ℝ}
    (hp : 2 ≤ p) (hsmall : p - 2 < recursiveFrameExponentTolerance n) :
    (2 : ℝ) ^ (2 - 4 / p) < recursiveLocalHilbertThreshold (3 * 2 ^ n) :=
  (Classical.choose_spec (exists_frameExponent_tolerance
    (recursiveLocalHilbertThreshold_gt_one (3 * 2 ^ n)))).2 p hp hsmall

/-- The actual recursive parameter sequence used by the construction. -/
def recursiveFrameSelection {η : ℝ} (hη : 0 < η) :
    RecursiveFrameSelection η recursiveFrameExponentTolerance :=
  Classical.choice (exists_recursiveFrameSelection hη recursiveFrameExponentTolerance_pos)

theorem recursiveFrameSelection_later_parallelogram {η : ℝ} (hη : 0 < η)
    {i j : ℕ} (hij : i < j) :
    (2 : ℝ) ^ (2 - 4 / ((recursiveFrameSelection hη).block j).exponent) <
      recursiveLocalHilbertThreshold (3 * 2 ^ ((recursiveFrameSelection hη).block i).order) :=
  recursiveFrameExponentTolerance_spec _
    ((recursiveFrameSelection hη).block j).two_lt_exponent.le
    ((recursiveFrameSelection hη).later_exponent_small i j hij)

end ComplementedSubspace
