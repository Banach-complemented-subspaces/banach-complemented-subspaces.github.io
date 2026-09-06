# Independent review of emitted lexical findings

Reviewed 2026-09-06, read-only, from `output/full_fresh_audit_2026-09-06_102854/evidence/identity-lexical-source-inventory.json` and `identity-lexical-occurrences.jsonl`, with concrete contexts read from the reproduced pinned sources. No Lean, build, scanner, or proof check was run for this review. This is not a final audit PASS: the final identity hashes, fresh replay and endpoint checks were still being coordinated separately.

## Counts and scope

| Recorded scope | Source files | All token hits | Code-class hits | Block comments | Line comments | Strings |
|---|---:|---:|---:|---:|---:|---:|
| project-imported | 177 | 195 | 127 | 65 | 3 | 0 |
| project-unrelated-or-audit | 53 | 10 | 6 | 2 | 1 | 1 |
| fresh-evidence-audit-only | 4 | 34 | 20 | 7 | 7 | 0 |
| external-built-module-source | 2,597 | 6,029 | 3,985 | 1,717 | 197 | 130 |
| Total | 2,831 | 6,268 | 4,138 | 1,791 | 208 | 131 |

The inventory records 34,779,293 bytes and 831,206 lines. External package source counts: Mathlib 2,340; Aesop 132; Batteries 74; Qq 14; Plausible 13; ImportGraph 10; ProofWidgets 10; LeanSearchClient 4. These are selected `.lean` files corresponding to built package modules, not an assertion that every declaration in every selected file is a transitive proof dependency of an endpoint. The 230 local project `.lean` files are partitioned into imported and other/audit scopes; this table is not the separate 233-entry frozen-file manifest check.

The lexer labels syntax/name quotations as `code`, so `executable_hits` in the inventory means lexical code-class hits, not proven execution. A bare keyword count cannot distinguish generated syntax, quoted constant names, inspected expressions, declarations and invoked tactics.

## Imported project and audit helper findings

There are **zero `project_gate` hits**. The only code-class hits in imported project sources are 124 `set_option` occurrences and three `allowUnsafeReducibility` occurrences. There are no recorded code-class `sorry`, `admit`, `admitted`, `sorryAx`, `axiom`, `native_decide`, `ofReduceBool`, `trust`, `trustLevel` or `skipKernelTC` tokens in that scope. Three `axiom` and five `admit` hits there occur in mathematical prose inside block comments.

The project options comprise 83 `backward.isDefEq.respectTransparency false` occurrences (two scoped with `in`), 13 `backward.isDefEq.respectTransparency.types false`, 18 `synthInstance.maxSize 256`, seven `maxHeartbeats` settings, and three scoped `allowUnsafeReducibility true` settings. The latter precede only local reducibility attributes:

- `ComplementedSubspace/ProductFrameMoments.lean:10–11`: `Matrix MomentIndex FrameIndex`.
- `ComplementedSubspace/ProductFrameSymmetry.lean:6–7`: `MomentIndex FrameIndex`.
- `ComplementedSubspace/ProductFrameTrace.lean:69–70`: `FrameCoefficient Matrix`.

These are actual elaborator/transparency settings, and must be reported; their spelling does not establish a kernel-check bypass. The fresh replay is the relevant check on the resulting declarations.

The other-local code hits are two `set_option`, three `run_cmd` (RealConstructionAudit, TensorMomentAudit, WholeProjectAudit), and one `constants` reference. Fresh evidence hits are three `set_option`, one `run_cmd`, three `constants`, three `unsafe`, seven `addDecl`, one `addDeclCore` and two `partial`. The latter include copied pinned Lean checker/replay implementation: for example `pinned-Replay.lean:60` calls `env.addDeclCore 0 0 d`; they are audit machinery, not imported project theorem source. Their correctness is a distinct checker implementation question.

## Every external code-class placeholder spelling

All paths in this section are relative to the indicated reproduced dependency package. These findings are retained rather than silently discarded.

| Token and location | Concrete interpretation |
|---|---|
| `sorryAx`, LeanSearchClient `LeanSearchClient/Syntax.lean:178` | `defaultTerm` actually constructs an expression with `mkAppM ``sorryAx #[type, mkConst ``false]` when the expected type has no expression metavariables. This is placeholder-generating search-tool scaffolding, not merely a comment or a recognizer. Its presence does not demonstrate use in an endpoint proof. |
| `admit`, Aesop `Aesop/Script/Step.lean:61`; `sorry`, line 62 | `Step.mkSorry` calls `preGoal.admit` inside a saved metaprogram state and constructs quoted tactic syntax `(tactic\| sorry)`. `Aesop/Tree/ExtractScript.lean:118,128` invokes it when extracting a safe-prefix script with unfinished goals/introduction metavariables. These are real incomplete-script construction capabilities. |
| `admit`, Mathlib `Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean:80,217,237` | All three are components of the option identifier `linter.style.admit`, used for registration and lint checks, not applications of the `admit` tactic. |
| `sorry`, Mathlib `Mathlib/Tactic/TFAE.lean:278,279,285` | Three expression quotations `q(sorry : ...)` are passed to `Term.addTermInfo'` to provide hover type information. The function computes and returns the proposition `ty`; the placeholder expressions here are information-tree metadata. |
| `sorry`, Mathlib `Mathlib/Tactic/Widget/Calc.lean:141,143` | The `calc?` elaborator creates a suggested `calc ... := by sorry`, then actually calls `evalTactic` on quoted `sorry`. Thus this is an interactive proof-scaffold tactic that can admit its current goal when invoked, not a harmless quotation alone. This review makes no claim it was invoked by project proofs. |
| `sorryAx`, Mathlib `Mathlib/Lean/Expr/Basic.lean:97,384` | Quoted constant names used by a blacklist predicate and an expression recognizer. |
| `sorryAx`, Mathlib `Mathlib/Lean/Meta/RefinedDiscrTree/Initialize.lean:117` | Quoted constant name rejected by the lemma-suggestion blacklist. |
| `sorryAx`, Mathlib `Mathlib/Util/PrintSorries.lean:71` | Quoted constant name tested while collecting and reporting existing placeholder dependencies. |

This exhausts the recorded external **six `sorry`, four `admit`, five `sorryAx`** code-class occurrences. There are zero external `admitted` code-class occurrences.

Additional placeholder-related code is also present: seven `mkSorry` occurrences (Aesop's declaration and two callers above; Batteries `Batteries/Tactic/Lint/Simp.lean:48`, constructing a dummy expression to inspect simp-theorem types; Mathlib `Mathlib/Lean/Expr/Basic.lean:218`, erasing proofs for expression analysis; `Mathlib/Tactic/Linter/UnusedInstancesInType.lean:160,172`, instantiating binder/let bodies for linter analysis). Five `hasSorry` occurrences implement or invoke detection: Aesop `RuleTac/Tactic.lean:94` explicitly rejects a generated proof containing sorry, Aesop `Util/Basic.lean:249` defines the detector, Batteries `Tactic/Lint/Misc.lean:45` checks both value and type, and Mathlib `Tactic/Linter/UnusedInstancesInType.lean:195` avoids checking placeholder-containing types. Such APIs can manipulate incomplete expressions within metaprograms; only dependency checking of the final mathematical declarations establishes whether a placeholder escaped into a proof.

## Axioms, native computation, trust and broader metaprogramming

External recorded code-class counts for **`axiom`, `native_decide`, `ofReduceBool`, `trust`, `trustLevel`, `skipKernelTC`, `debug.skipKernelTC` are all zero**. The actual non-code hits are:

- `axiom`: 42 block-comment, three line-comment and two string occurrences.
- `native_decide`: five block-comment occurrences and one diagnostic string. One comment documents a computational primality test; the remaining contexts concern Mathlib's deprecated-syntax linter and its prohibition of native proof tactics.
- `ofReduceBool`: one line comment, `Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean:89`, explaining that native checks concern more than this one axiom.
- `trust`: one Aesop GoalDiff prose line comment and one Mathlib native-tactic linter block comment.
- No recorded `trustLevel` or `skipKernelTC` occurrences in any lexical kind.

External placeholder prose/string counts are: `sorry` 94 block comments + nine line comments + 23 strings; `admit` 30 block comments + two strings; `sorryAx` six block comments. These do not constitute admitted mathematical declarations.

Broader external code-class counts include `meta` 1,205, `unsafe` 147, `partial` 379, `opaque` 28, `implemented_by` 15, `unsafeCast` two, `addAndCompile` eight, `addDecl` 31, `setEnv` ten, `modifyEnv` 26, `evalExpr` 17, `evalConst` six, `lcProof` 11, and one `reduceNat` token (the identifier `reduceNat?` in a click-suggestion simplifier). They are reportable implementation mechanisms, not by themselves mathematical axioms or proof failures. This bounded review inspected all listed critical placeholder/native/trust contexts, not every one of the thousands of general metaprogramming occurrences.

## What this review establishes

The emitted lexical evidence shows no gated imported-project occurrence and identifies concrete external placeholder-generating tooling that must remain visible in the report. It does **not** establish absence of generated problematic terms, justify a blanket rejection of library implementation code, prove successful compilation/replay, establish final source identity, or determine endpoint proof trust. Those conclusions depend on the actual completed fresh build/replay and on the five endpoints' transitive axiom results (with the permitted `propext`, `Classical.choice`, `Quot.sound` allowlist), plus the final manifest/identity checks. No PASS is inferred here from scan output appearing before its final checks finish.
