import ComplementedSubspace.TensorMoment
import Lean.Util.CollectAxioms

#print axioms ComplementedSubspace.symmetric_bilinear_norm_bound
#print axioms ComplementedSubspace.rankOne_mixed_hsSq_bound
#print axioms ComplementedSubspace.circleLift_rankOne_bound
#print axioms ComplementedSubspace.tensorMoment_rankOne_bound
#print axioms ComplementedSubspace.tensor_paired_column_moments_bound

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`ComplementedSubspace.symmetric_bilinear_norm_bound,
      `ComplementedSubspace.rankOne_mixed_hsSq_bound,
      `ComplementedSubspace.circleLift_rankOne_bound,
      `ComplementedSubspace.tensorMoment_rankOne_bound,
      `ComplementedSubspace.tensor_paired_column_moments_bound] do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
  logInfo "All five new tensor proofs passed the standard-axiom allowlist audit."
