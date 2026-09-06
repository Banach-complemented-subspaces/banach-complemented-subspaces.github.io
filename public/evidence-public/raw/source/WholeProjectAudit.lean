import ComplementedSubspace
import Lean.Util.CollectAxioms

#print axioms ComplementedSubspace.realMainTheorem
#print axioms ComplementedSubspace.realCorollary
#print axioms ComplementedSubspace.realUnconditionalCorollary
#print axioms ComplementedSubspace.realSeparableNonprimarity
#print axioms ComplementedSubspace.complexCorollary

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`ComplementedSubspace).isPrefixOf name then
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax => !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "Unexpected axioms in {name}: {unexpected}"
      count := count + 1
  logInfo m!"Audited {count} declarations in ComplementedSubspace. All transitive axioms are in the allowlist: propext, Classical.choice, Quot.sound."
