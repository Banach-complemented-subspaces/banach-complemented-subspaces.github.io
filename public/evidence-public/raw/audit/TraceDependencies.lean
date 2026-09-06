import ComplementedSubspace
import Lean

/-!
Audit-only code. It neither introduces a mathematical assumption nor edits the proof.
Run only after the project has been rebuilt. All generated artifacts stay beside this file.
The traversal follows the pinned Lean collectAxioms edge convention, but does not use
its imported-module axiom cache: it inspects every reachable declaration directly.
-/

open Lean Meta Elab Command

namespace IndependentDependencyAudit

private def outputDirectory : System.FilePath :=
  "LEAN_PROJECT/verification/independent-audit-2026-09-05"

private def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient_primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def expectedBody (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
  | _ => false

private def origin (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.allImportedModuleNames[idx.toNat]?

private def projectModule (name : Name) : Bool :=
  name == `ComplementedSubspace || (`ComplementedSubspace).isPrefixOf name ||
  name == `BanLat || (`BanLat).isPrefixOf name

private def sortedNames (s : NameSet) : Array String :=
  (s.toArray.qsort Name.lt).map Name.toString

private def jsonLine (h : IO.FS.Handle) (fields : List (String × Json)) : IO Unit :=
  h.putStrLn (Json.mkObj fields).compress

private def inspect : MetaM Unit := do
  let target := `ComplementedSubspace.realMainTheorem
  let env := (← getEnv).setExporting false
  let some targetInfo := env.checked.get.find? target
    | throwError "Audit target is missing from the checked environment: {target}"
  unless kind targetInfo == "theorem" do
    throwError "Audit target is not a theorem declaration: {target}"
  let targetType ← ppExpr targetInfo.type
  let expandedTargetType ← ppExpr (← whnf targetInfo.type)
  let stockAxioms ← collectAxioms target
  let stockSet := stockAxioms.foldl (fun s n => s.insert n) ({} : NameSet)
  liftM (m := IO) (n := MetaM) <| IO.FS.createDirAll outputDirectory
  let nodeFile ← liftM (m := IO) (n := MetaM) <| IO.FS.Handle.mk (outputDirectory / "dependency_nodes.jsonl") .write
  let edgeFile ← liftM (m := IO) (n := MetaM) <| IO.FS.Handle.mk (outputDirectory / "dependency_edges.jsonl") .write
  let directFile ← liftM (m := IO) (n := MetaM) <| IO.FS.Handle.mk (outputDirectory / "dependency_direct.jsonl") .write
  let mut queue : Array Name := #[target]
  let mut seen : NameSet := ({} : NameSet).insert target
  let mut cursor : Nat := 0
  let mut edgeCount : Nat := 0
  let mut localCount : Nat := 0
  let mut checkedCount : Nat := 0
  let mut axioms : NameSet := {}
  let mut missing : NameSet := {}
  let mut missingBodies : NameSet := {}
  let mut missingOrigins : NameSet := {}
  let mut localSuspicious : Array Json := #[]
  let mut localModules : NameSet := {}
  let maxNodes := 300000
  let maxEdges := 4000000
  while cursor < queue.size && cursor < maxNodes && edgeCount < maxEdges do
    let name := queue[cursor]!
    cursor := cursor + 1
    match env.checked.get.find? name with
    | none =>
      missing := missing.insert name
      liftM (m := IO) (n := MetaM) <| jsonLine nodeFile [
        ("name", toJson name.toString), ("status", toJson "missing_checked_constant")]
    | some ci =>
      checkedCount := checkedCount + 1
      let mod := origin env name
      let isLocal := mod.any projectModule
      if mod.isNone then
        missingOrigins := missingOrigins.insert name
      if isLocal then
        localCount := localCount + 1
        if let some modName := mod then
          localModules := localModules.insert modName
      let body := ci.value? (allowOpaque := true)
      if expectedBody ci && body.isNone then
        missingBodies := missingBodies.insert name
      let suspicious := isLocal &&
        (ci.isAxiom || ci.isUnsafe || ci.isPartial || kind ci == "opaque")
      let mut suspiciousType : Json := Json.null
      let mut suspiciousIsProp : Json := Json.null
      if suspicious then
        suspiciousType := toJson (← ppExpr ci.type).pretty
        suspiciousIsProp := toJson (← isProp ci.type)
      let node := [
        ("name", toJson name.toString),
        ("status", toJson "checked_constant_present"),
        ("origin_module", toJson (mod.map Name.toString)),
        ("project_owned", toJson isLocal),
        ("kind", toJson (kind ci)),
        ("unsafe", toJson ci.isUnsafe),
        ("partial", toJson ci.isPartial),
        ("body_expected", toJson (expectedBody ci)),
        ("body_available", toJson body.isSome),
        ("suspicious_type", suspiciousType),
        ("suspicious_type_is_prop", suspiciousIsProp)]
      liftM (m := IO) (n := MetaM) <| jsonLine nodeFile node
      if suspicious then
        localSuspicious := localSuspicious.push (Json.mkObj node)
      if ci.isAxiom then
        axioms := axioms.insert name
      let mut groups : Array (String × Array Name) := #[]
      -- Quotient declarations are kernel primitives, matching stock collectAxioms.
      if kind ci != "quotient_primitive" then
        groups := groups.push ("type", ci.type.getUsedConstants)
      if let some value := body then
        groups := groups.push ("value", value.getUsedConstants)
      if let .inductInfo val := ci then
        groups := groups.push ("inductive_constructor", val.ctors.toArray)
      for (edgeKind, dependencies) in groups do
        for dependency in dependencies do
          edgeCount := edgeCount + 1
          let fields := [
            ("from", toJson name.toString), ("edge_kind", toJson edgeKind),
            ("to", toJson dependency.toString)]
          liftM (m := IO) (n := MetaM) <| jsonLine edgeFile fields
          if name == target then
            let dependencyInfo := env.checked.get.find? dependency
            let dependencyOrigin := origin env dependency
            liftM (m := IO) (n := MetaM) <| jsonLine directFile (fields ++ [
              ("origin_module", toJson (dependencyOrigin.map Name.toString)),
              ("project_owned", toJson (dependencyOrigin.any projectModule)),
              ("kind", toJson (dependencyInfo.map kind))])
          unless seen.contains dependency do
            seen := seen.insert dependency
            queue := queue.push dependency
  nodeFile.flush
  edgeFile.flush
  directFile.flush
  let complete := cursor == queue.size && missing.isEmpty && missingBodies.isEmpty
  let ownershipComplete := missingOrigins.isEmpty
  let actualAxioms := sortedNames axioms
  let expectedAxioms := sortedNames stockSet
  let axiomAgreement := actualAxioms == expectedAxioms
  let summary := Json.mkObj [
    ("target", toJson target.toString),
    ("target_kind", toJson (kind targetInfo)),
    ("target_type", toJson targetType.pretty),
    ("target_type_whnf", toJson expandedTargetType.pretty),
    ("target_level_parameters", toJson (targetInfo.levelParams.map Name.toString)),
    ("traversal_complete", toJson complete),
    ("ownership_classification_complete", toJson ownershipComplete),
    ("queued_nodes", toJson queue.size), ("processed_nodes", toJson cursor),
    ("checked_constants", toJson checkedCount), ("edges", toJson edgeCount),
    ("project_constants", toJson localCount),
    ("project_origin_modules", toJson (sortedNames localModules)),
    ("node_budget", toJson maxNodes), ("edge_budget", toJson maxEdges),
    ("missing_checked_constants", toJson (sortedNames missing)),
    ("missing_expected_bodies", toJson (sortedNames missingBodies)),
    ("constants_without_import_origin", toJson (sortedNames missingOrigins)),
    ("reachable_axioms_direct_traversal", toJson actualAxioms),
    ("reachable_axioms_stock_collectAxioms", toJson expectedAxioms),
    ("axiom_cross_check_agrees", toJson axiomAgreement),
    ("reachable_project_axiom_opaque_unsafe_partial", toJson localSuspicious),
    ("edge_semantics", toJson "Types and values for definitions/theorems/opaque declarations; types for axioms/constructors/recursors; types and constructor edges for inductives; quotient primitives are leaves. Values requested with allowOpaque=true. No imported axiom cache is used by this traversal.")]
  liftM (m := IO) (n := MetaM) <| IO.FS.writeFile (outputDirectory / "kernel_dependency_summary.json") summary.pretty
  liftM (m := IO) (n := MetaM) <| IO.FS.writeFile (outputDirectory / "dependency_trace.txt")
    s!"Target: {target}\nType: {targetType.pretty}\nExpanded target type: {expandedTargetType.pretty}\nTraversal complete: {complete}\nChecked constants: {checkedCount}\nProject constants: {localCount}\nEdges: {edgeCount}\nDirectly traversed axioms: {actualAxioms}\nStock collectAxioms: {expectedAxioms}\nAxiom lists agree: {axiomAgreement}\nMissing constants: {sortedNames missing}\nMissing expected bodies: {sortedNames missingBodies}\nLocal suspicious constants: {localSuspicious.size}\nRaw nodes: dependency_nodes.jsonl\nRaw typed edges: dependency_edges.jsonl\nDirect references: dependency_direct.jsonl\nStructured summary: kernel_dependency_summary.json\n"
  logInfo m!"Dependency audit: {checkedCount} constants; {localCount} project constants; {edgeCount} edges. Complete={complete}; stock axiom cross-check={axiomAgreement}; local suspicious={localSuspicious.size}."
  unless complete do
    throwError "Dependency traversal is incomplete; inspect kernel_dependency_summary.json"
  unless ownershipComplete do
    throwError "Dependency origin classification is incomplete; inspect constants_without_import_origin in kernel_dependency_summary.json"
  unless axiomAgreement do
    throwError "Dependency traversal disagrees with stock collectAxioms; inspect kernel_dependency_summary.json"

end IndependentDependencyAudit

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
run_cmd liftTermElabM do
  IndependentDependencyAudit.inspect
