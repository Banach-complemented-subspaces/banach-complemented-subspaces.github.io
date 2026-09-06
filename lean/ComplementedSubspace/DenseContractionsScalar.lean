import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Strong convergence of contractions fixed eventually on a dense subset -/

namespace ComplementedSubspace

open Filter Topology

theorem tendsto_contractions_of_dense_over
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {ι : Type*} (l : Filter ι) (T : ι → E →L[𝕜] E)
    (hT : ∀ i x, ‖T i x‖ ≤ ‖x‖)
    {S : Set E} (hS : Dense S)
    (hfix : ∀ y ∈ S, ∀ᶠ i in l, T i y = y) (x : E) :
    Tendsto (fun i => T i x) l (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy, hdist⟩ := hS.exists_dist_lt x (half_pos hε)
  filter_upwards [hfix y hy] with i hi
  have hclose : ‖x - y‖ < ε / 2 := by simpa only [dist_eq_norm] using hdist
  rw [dist_eq_norm]
  calc
    ‖T i x - x‖ = ‖T i (x - y) + (y - x)‖ := by
      rw [map_sub, hi]
      congr 1
      exact (sub_add_sub_cancel (T i x) y x).symm
    _ ≤ ‖T i (x - y)‖ + ‖y - x‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖y - x‖ := add_le_add (hT i (x - y)) le_rfl
    _ = ‖x - y‖ + ‖x - y‖ := by rw [norm_sub_rev y x]
    _ < ε := (add_lt_add hclose hclose).trans_eq (add_halves ε)

end ComplementedSubspace

