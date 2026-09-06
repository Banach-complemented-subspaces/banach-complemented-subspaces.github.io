import ComplementedSubspace.RecursiveDiagonalDPR
import ComplementedSubspace.RecursiveDiagonalDualDPR
import ComplementedSubspace.RecursiveDiagonalBidualDPR
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Name := #[
    `ComplementedSubspace.finite_selected_trace_obstruction,
    `ComplementedSubspace.frame_block_le_chiDPR,
    `ComplementedSubspace.frame_product_le_chiDPR_dual,
    `ComplementedSubspace.frame_product_le_chiDPR_bidual,
    `ComplementedSubspace.recursiveDiagonalRange_chiDPR_eq_top,
    `ComplementedSubspace.recursiveDiagonalRange_dual_chiDPR_eq_top,
    `ComplementedSubspace.recursiveDiagonalRange_bidual_chiDPR_eq_top]
  for name in names do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
    logInfo m!"{name}: {axioms}"
