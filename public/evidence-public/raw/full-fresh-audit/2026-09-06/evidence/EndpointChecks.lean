import ComplementedSubspace
import Lean.Util.CollectAxioms

set_option pp.fullNames true

#check (ComplementedSubspace.realMainTheorem : ComplementedSubspace.RealMainTheoremStatement)
#check (ComplementedSubspace.realCorollary : ComplementedSubspace.RealCorollaryStatement)
#check (ComplementedSubspace.realUnconditionalCorollary : ComplementedSubspace.UnconditionalCorollaryStatement ℝ)
#check (ComplementedSubspace.realSeparableNonprimarity : ComplementedSubspace.SeparableNonprimarityStatement)
#check (ComplementedSubspace.complexCorollary : ComplementedSubspace.ComplexCorollaryStatement)

#print axioms ComplementedSubspace.realMainTheorem
#print axioms ComplementedSubspace.realCorollary
#print axioms ComplementedSubspace.realUnconditionalCorollary
#print axioms ComplementedSubspace.realSeparableNonprimarity
#print axioms ComplementedSubspace.complexCorollary

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let endpoints : Array Name := #[`ComplementedSubspace.realMainTheorem,
    `ComplementedSubspace.realCorollary, `ComplementedSubspace.realUnconditionalCorollary,
    `ComplementedSubspace.realSeparableNonprimarity, `ComplementedSubspace.complexCorollary]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in endpoints do
    match env.checked.get.find? name with
    | some (.thmInfo info) =>
      unless info.levelParams.isEmpty do
        throwError "Unexpected universe parameters in {name}"
      if info.type.isForall then
        throwError "Unexpected theorem parameters in {name}"
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax => !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "Unexpected transitive axioms in {name}: {unexpected}"
      logInfo m!"ENDPOINT: {name}; kind=theorem; no universe or theorem parameters; stored type={info.type}; axioms={axioms}"
    | _ => throwError "Missing theorem declaration: {name}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`ComplementedSubspace).isPrefixOf name then
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax => !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "Unexpected axioms in {name}: {unexpected}"
      count := count + 1
  logInfo m!"NAMESPACE AXIOM AUDIT: {count} imported ComplementedSubspace declarations; allowlist propext, Classical.choice, Quot.sound."
