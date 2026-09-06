# Endpoint and presentation checks for a fresh isolated audit

Read-only source inspection of `output/lean_trial_2026-09-05` and the existing local companion-site checks. No Lean command, rebuild, dependency traversal, scan or website check was executed for this research task. No mathematics, website content or original evidence was changed.

## Root coverage confirmed from source

`ComplementedSubspace.lean` lines 75–77 explicitly imports `ComplementedSubspace.RealMainTheorem`, `ComplementedSubspace.RealMainConsequences` and `ComplementedSubspace.ComplexCorollary`. Those modules define all five actual endpoints inside `namespace ComplementedSubspace`:

| Fully qualified endpoint | Exact declared type | Source declaration |
|---|---|---|
| `ComplementedSubspace.realMainTheorem` | `ComplementedSubspace.RealMainTheoremStatement` | `ComplementedSubspace/RealMainTheorem.lean:15` |
| `ComplementedSubspace.realCorollary` | `ComplementedSubspace.RealCorollaryStatement` | `ComplementedSubspace/RealMainConsequences.lean:22` |
| `ComplementedSubspace.realUnconditionalCorollary` | `ComplementedSubspace.UnconditionalCorollaryStatement ℝ` | `ComplementedSubspace/RealMainConsequences.lean:39` |
| `ComplementedSubspace.realSeparableNonprimarity` | `ComplementedSubspace.SeparableNonprimarityStatement` | `ComplementedSubspace/RealMainConsequences.lean:54` |
| `ComplementedSubspace.complexCorollary` | `ComplementedSubspace.ComplexCorollaryStatement` | `ComplementedSubspace/ComplexCorollary.lean:18` |

All five source declarations are theorems with closed statement headers. The declaration `separableNonprimarity_of_realMainTheorem` has a hypothesis, but it is an intermediate lemma, not the closed endpoint `realSeparableNonprimarity`. Fresh checks should distinguish them explicitly.

## Reuse these checks after the isolated build

1. **`WholeProjectAudit.lean` — reusable unchanged.** It imports the integration root, prints the axioms of all five endpoints (lines 4–8), then calls `Lean.collectAxioms` for every imported declaration whose name has the `ComplementedSubspace` namespace prefix. It throws on any axiom outside `propext`, `Classical.choice`, `Quot.sound`. Capture the actual new count; do not hard-code the historical 2,573. Its namespace loop is not literally an inventory of every declaration from every local origin module, although recursive axiom collection follows private and library dependencies reachable from the audited names.

2. **`verification/independent-audit-2026-09-05/MainIdentity.lean` — reuse its inspection method, extend only in a new audit-only helper.** The existing helper checks only `realMainTheorem`: `#check`, explicit type ascription, a proof example, `.thmInfo` kind in `env.checked`, exact stored type and no universe parameters. A fresh combined helper should `import ComplementedSubspace` and perform the same kind/closed-type checks for all five names above. Elaborate the expected type expression before comparing it with `info.type`, especially for `UnconditionalCorollaryStatement ℝ`, whose expression includes the inferred field instance. That expected type is an application, not just `mkConst` of a statement name. Require `.thmInfo`, no unexpected level parameters, and the exact closed expected type; retain the printed fully qualified type for review.

   The proof-type part can use these five explicit examples, with no assumptions:

   ```lean
   import ComplementedSubspace

   example : ComplementedSubspace.RealMainTheoremStatement :=
     ComplementedSubspace.realMainTheorem
   example : ComplementedSubspace.RealCorollaryStatement :=
     ComplementedSubspace.realCorollary
   example : ComplementedSubspace.UnconditionalCorollaryStatement ℝ :=
     ComplementedSubspace.realUnconditionalCorollary
   example : ComplementedSubspace.SeparableNonprimarityStatement :=
     ComplementedSubspace.realSeparableNonprimarity
   example : ComplementedSubspace.ComplexCorollaryStatement :=
     ComplementedSubspace.complexCorollary
   ```

   These examples are recommended source text, not newly claimed successful checks. Keep the stored-kind/type inspection as well: an example by itself is not a complete report of the declaration's exact stored shape.

3. **`PrintAxioms.lean` — main-only and informational.** It prints the real main theorem's axioms and the three allowed foundation axioms. The all-five prints and enforcement already in `WholeProjectAudit.lean` are the primary reusable axiom check; this file is optional explanatory output. A successful `#print axioms` alone does not enforce an allowlist.

4. **`PrintDefinitions.lean` — reuse/extend an audit-only copy.** Its fully qualified, universe-explicit output covers the real main statement, range/lattice predicates, blocks and real local constants. Add prints for `GLFactorization.cost`, `BanachModel`, `HasUnconditionalSchauderBasis`, `IsOneUnconditional`, `HasOneUnconditionalSchauderBasis`, `IsSuperreflexiveByRenorming`, `IsIsomorphicToRealBanachLattice`, and all five statement definitions: `RealMainTheoremStatement`, `UnconditionalCorollaryStatement`, `RealCorollaryStatement`, `ComplexCorollaryStatement`, `SeparableNonprimarityStatement`. This captures the actual elaborated formulations, not an English-faithfulness claim.

5. **`MainTheoremReview.lean` — reusable unchanged as formulation identity.** Its `rfl` examples at lines 71–72 compare the displayed real DPR/GL aliases with the actual definitions; line 120 compares the displayed main proposition with `RealMainTheoremStatement`. It imports only the statement module and does not prove the existence theorem. Run it as a separate review check against the freshly rebuilt modules.

6. **`MainRealTheoremDefinitions.lean` — optional standalone elaboration check only.** It imports Mathlib and recreates project definitions in the original `ComplementedSubspace` namespace. It has no theorem proof and no equality checks against the imported project. Compile it in a separate invocation, without importing it together with the root, which would duplicate names. A successful run is standalone definitional well-formedness, not identity with the project or a proof of the main theorem.

Use the isolated project's pinned Lake/Lean, with that project as working directory. The exact existing audit invocation pattern is:

```text
lake --no-cache env lean -j1 -M8192 WholeProjectAudit.lean
lake --no-cache env lean -j1 -M8192 <new-audit-only-all-five-identity-helper>.lean
lake --no-cache env lean -j1 -M8192 <new-audit-only-print-definitions-helper>.lean
lake --no-cache env lean -j1 -M8192 MainTheoremReview.lean
lake --no-cache env lean -j1 -M8192 MainRealTheoremDefinitions.lean
```

Record exit code, command, working directory, selected toolchain, timestamps and unaltered output for each actual run. These imported-endpoint checks and expression inspections do **not** themselves replay all imported proofs through the kernel. The fresh build and any separately requested kernel replay require separate evidence and status.

## Placeholder/source and dependency helpers: path/scope cautions

- **`placeholder_scan.py` is useful lexical analysis, but must be copied/adapted into the new audit.** `OUT` is its script directory; `ROOT = OUT.parent.parent`; `MAIN` is hard-coded to `ComplementedSubspace.RealMainTheorem`. It scans all local `.lean` files, including scratch/audits/vendored code, excluding `.lake/packages` and `.lake/build`; it separately classifies the local syntactic import closure of that single `MAIN`. For all-five/root scope, use the integration root as the closure seed in the new helper, or record all three endpoint-module closures, and rename the misleading `in_realMainTheorem_import_closure` report keys. Do not claim that the scanner covers downloaded dependencies. Its pinned Lean `ReducibilityAttrs.lean` evidence path at lines 303–308 also depends on the old workspace layout and must point to the chosen isolated runtime/source copy.
- **An exit code of zero from this scanner is not a “no placeholders” gate.** Lines 390–391 fail on lexing/import errors, symlinks, source changes or inventory disagreement, but the script reports rather than automatically rejects the hazard list. Review or explicitly gate `source_placeholder_or_trust_hazards`, dynamic commands and options against the declared compiled scope. Keep comments/string hits, unused scratch hits and active imported-code hits distinguished. The scanner includes self-tests for nested comments, strings/interpolation and quoted identifiers; retain them. Its hard-coded narrative about historical counts of `run_cmd`/option occurrences must be updated or omitted in the new report rather than copied as a fresh observation.
- **`TraceDependencies.lean` is an audit-only expression traversal, not kernel replay.** It imports the root but selects only `realMainTheorem` at line 47 and writes to a hard-coded original audit directory at lines 16–17. Never run that file unmodified if old evidence must remain frozen. A new audit copy can take all five targets, preferably sharing a union traversal to avoid duplicating large external dependency graphs while retaining per-target root/type/axiom results. It follows types, available bodies and inductive-constructor edges, compares directly found axioms with stock `collectAxioms`, and fails on incomplete traversal, missing origin classification or disagreement. However, it records `localSuspicious` and does **not** fail merely because that list is nonempty; retain the independent allowlist check and review local axiom/unsafe/partial/opaque records explicitly. Its resource caps must be reported if reached, never relabeled as complete.
- **`review_dependency_graph.py`** reads/writes beside itself, and consumes the trace plus a source map containing absolute paths. It can review new graph artifacts only after those inputs/path references are regenerated for the new isolated run. It is not a substitute for running Lean or replaying proofs.
- **Do not reuse `run_independent_audit.ps1` or its resume wrapper in place.** They infer the original project/runtime/evidence layout and write old named logs/status files; the original clean/build plan explicitly retained external dependency caches. They are historical orchestration for a narrower freshness claim, not a ready-made full fresh build wrapper. Reuse individual checked audit sources in the isolated run and record new evidence separately.

## Website and definitions identity

No helper literally named `check-review` was found in the inspected project/site/research helpers. The existing applicable checks are:

| Helper | What it checks / required fresh-audit adaptation |
|---|---|
| `tmp/companion-site-research/check_site_math_literals.py` | Compares 5 endpoint literals, 5 statement literals and the 20 project definition snippets with recorded source ranges; checks paper-derived site text against the local mapping. It hard-codes site/project/output paths, normalizes via `splitlines` and `.strip`, and does not set a failing exit status on mismatches. Copy its comparison logic into the new audit, point at the isolated source and read-only site snapshot, write new output, and fail explicitly on mismatches. |
| Site `scripts/check-guides.mjs` | Checks clause anchors/coverage, snippets against source, original source hashes, asset hashes and TeX. It reads absolute original source references, hard-codes `../lean_trial_2026-09-05`, and writes `qa/consolidated-source-check.json`; do not run it in the original site for this audit. An audit-only copy can resolve recorded relative source paths against the isolated tree and place output in new evidence. |
| Site `scripts/check-displayed-source.mjs` | Browser/clipboard comparison on a local preview, plus definition context display. It is presentation testing, writes site QA output, and is outside the mathematical fresh-build requirement. Existing evidence should remain untouched. |

For the new audit, compare **all** displayed source material: `content/evidence.json` endpoint/statement/predicate literals and their contexts; `content/definitions.json` project and standard-Mathlib snippets and contexts; source-download bytes and relevant manifests. Use exact byte equality for copies and a separately declared newline-only normalization policy for displayed strings, rather than silently calling `.strip()` comparisons byte-exact. Resolve Mathlib source against the isolated pinned dependency revision, not current upstream documentation.

The site displays actual project snippets rather than new mathematical wrappers, so literal/source-hash comparison is the appropriate general identity check. If an extra Lean presentation check is desired, extract only proposition bodies into fresh audit-only names and prove their equality to the actual statement constants by `rfl`; do not redefine the project's structures and claim those new nominal types are definitionally identical. Existing `MainTheoremReview.lean` already supplies the real-main formulation comparison. English/manuscript correspondence remains a separate mathematical review.
