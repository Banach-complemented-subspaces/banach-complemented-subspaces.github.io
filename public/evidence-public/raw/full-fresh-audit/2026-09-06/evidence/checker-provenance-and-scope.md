# Pinned Lean checker: interface, scope and provenance

Research only: read the full fresh-audit brief and the installed Lean **4.34.0-rc2** sources; hashed existing files. No replay, compilation, source/audit/site mutation, or expensive check was executed.

## Command ready for the initial replay

Run from the frozen project's root, using its Lake environment and the exact pinned executable:

```powershell
& 'WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/bin/lake.exe' env 'WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/bin/leanchecker.exe' --fresh --verbose ComplementedSubspace
```

The expected verbose start line is `replaying ComplementedSubspace with --fresh`. The successful branch returns native process exit code **0**; it does not print a PASS banner, elapsed time, count, or per-declaration progress. Preserve actual stdout/stderr and the actual native exit status; an interrupted or still-running checker is not a pass.

**Use explicit target `ComplementedSubspace`.** With no positional argument this CLI guesses a module by capitalizing the package name from `lake-manifest.json`, which is inappropriate for the differently named package here. The live root's final three imports are `ComplementedSubspace.RealMainTheorem`, `ComplementedSubspace.RealMainConsequences`, and `ComplementedSubspace.ComplexCorollary`; these contain the five expected endpoints. Root should still record the resolved `.olean` and repeat actual endpoint checks.

**Do not use `--help`, `--version`, `-j…`, or `-M…` as checker controls.** This pinned CLI only interprets `--fresh` and `-v`/`--verbose`. Other dash-prefixed arguments are silently discarded, rather than validated. In particular, `leanchecker --help` alone can attempt a real default-target check. Use an external audit-owned bounded runner for wall-clock/resource limits. No help/version probe was run during this research.

Source: [installed LeanChecker.lean:70](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/LeanChecker.lean:70>), especially lines 75–104 and 114; [matching pinned official source](https://github.com/leanprover/lean4/blob/6a10ac8c22beadecabdbb0919c2b50214762f91d/src/LeanChecker.lean#L70-L114).

## Exact fresh-replay semantics

- `replayFromFresh` imports the named root, then passes **`env.constants.map₁`** to **`(mkEmptyEnvironment).toKernelEnv.replay`**. This includes the imported environment, not merely the final theorem wrapper or its transitive proof graph. Fresh selection requires a single exact module; the non-fresh mode instead permits a prefix and reuses the already imported environment.
- `withImportModules` uses no loaded environment extensions and defaults to **private** `.olean` level, which loads all module data as if module-visibility annotations were absent. `mkEmptyEnvironment` constructs an empty constants map with default **trust level 0**.
- There is **no package-name/core-module exclusion** in the fresh replay loop. Imported safe logical declarations from the retained Lean/Init/Std toolchain are included as they occur in the imported constant map. The executable/runtime and toolchain artifacts remain the retained baseline; their retention is not a source rebuild or a separate implementation of the kernel.
- Replay schedules declarations in dependency order using their type and available value references, including opaque values (`allowOpaque := true`). Definitions, theorems, axioms and opaque declarations are submitted through `Kernel.Environment.addDeclCore 0 0 …`; this is the kernel-checking API, not `addDeclWithoutChecking`.
- Mutual inductives are reconstructed and submitted as inductive declarations. Stored constructors and recursors are checked for equality against those generated after inductive replay. Quotient declarations use the kernel's quotient primitive after ensuring `Eq` has been replayed.
- **Unsafe and partial constants are deliberately skipped** by the official implementation. `isPartial` means a definition with `.partial` safety. `isUnsafe` examines declaration safety flags; it does not mean every declaration from a module containing unsafe code is skipped. Do not describe replay as a mathematical correctness proof of unsafe implementation functions.
- A duplicate-theorem case can skip an already-present theorem when its name, type, level parameters and mutual-block list match; this is the official module/private-theorem duplicate handling. Do not alter it or suppress errors by deleting declarations.
- Axioms are added as axioms. Replay does not prove them or enforce the project's allowlist: repeat the five endpoint transitive-axiom checks independently.

Primary local sources:

| Behavior | Source |
|---|---|
| Fresh imported-map replay | [LeanChecker.lean:36](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/LeanChecker.lean:36>) |
| Empty environment / trust 0 | [Lean/Environment.lean:1530](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/Lean/Environment.lean:1530>) |
| Private import level; no loaded extensions | [Lean/Environment.lean:2438](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/Lean/Environment.lean:2438>) and :2457 |
| Kernel checking call | [Lean/Replay.lean:59](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/Lean/Replay.lean:59>); [Lean/Environment.lean:295](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/Lean/Environment.lean:295>) |
| Declaration cases, duplicates, quotient primitive | [Lean/Replay.lean:74](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/Lean/Replay.lean:74>) |
| Constructor/recursor comparison | [Lean/Replay.lean:148](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/Lean/Replay.lean:148>) |
| Unsafe/partial skip | [Lean/Replay.lean:175](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/Lean/Replay.lean:175>); [Lean/Declaration.lean:452](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/Lean/Declaration.lean:452>) |
| Type/body dependencies, opaque bodies included | [Lean/Util/FoldConsts.lean:67](<WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/Lean/Util/FoldConsts.lean:67>) |

Public pinned source links: [LeanChecker.lean](https://github.com/leanprover/lean4/blob/6a10ac8c22beadecabdbb0919c2b50214762f91d/src/LeanChecker.lean), [Lean/Replay.lean](https://github.com/leanprover/lean4/blob/6a10ac8c22beadecabdbb0919c2b50214762f91d/src/Lean/Replay.lean), [Lean/Environment.lean](https://github.com/leanprover/lean4/blob/6a10ac8c22beadecabdbb0919c2b50214762f91d/src/Lean/Environment.lean). Findings above come from the installed matching sources; no checker changes were made.

## Provenance and current hashes

Runtime root: `WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows`.

The local `lean-release.json` records the official [v4.34.0-rc2 release](https://github.com/leanprover/lean4/releases/tag/v4.34.0-rc2), published 2026-08-21, and [Windows tar.zst asset](https://github.com/leanprover/lean4/releases/download/v4.34.0-rc2/lean-4.34.0-rc2-windows.tar.zst). Its stored asset size is **588,884,754 bytes**. The archive was rehashed during this read-only inspection and matches the SHA256 in that stored release metadata.

| Existing file (relative to runtime root unless noted) | Current SHA256 |
|---|---|
| `bin/leanchecker.exe` | `b7c503a7a984f32f04c1badb79e53e350ddb72aed530da12699e4b06357ce149` |
| `bin/lean.exe` | `37dfe799f69b990251f3b6bcff8a1c10c1afe2adcdecc5c580cc6726ffb63433` |
| `bin/lake.exe` | `5afaf2ad866c1aa6c1eda7bdb84ebd99e1de8be3a95a219094654dfa00b47c0a` |
| `src/lean/LeanChecker.lean` | `2d18ec111d73c536b0bdee2533556bb9548c349f386797d3d3837b1f84d55dae` |
| `src/lean/Lean/Replay.lean` | `c434b5b2bc5047ca58d4a095fcf1d9935d413c788ae98a4f21948e6a95ca3fb0` |
| Sibling archive `lean-4.34.0-rc2-windows.tar.zst` | `b777ecceb5edf651ee0840b7ef455098844b44203bad09310a661cf1a73ffb10` |

The Lean/Lake executable hashes agree with the previous recorded environment. These hashes identify the bytes inspected; no new compiler bootstrap or independent signature certification was performed. Root should capture current native `lean --version` / `lake --version` outputs and search paths as part of the actual audit command evidence.

## Official reference and reporting limits

Opened the brief's official [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) reference. It explains stored `.olean` replay, distinguishes it from axiom listing and mathematical interpretation, and notes that replay uses Lean's own kernel and assumes structurally valid `.olean` data. Its prose still names `lean4checker`; **the installed pinned source and executable take precedence**, establishing `leanchecker.exe` and the interface above.

Do not reuse the previous **40,291-node main-theorem proof graph** count as this checker's replay count. Fresh checking targets the integration root's entire imported constant map, a different scope, and this official executable prints no count. If coverage statistics are desired, report separately measured inventory figures labelled as inventory, not as counts emitted by replay.

Keep initial artifact replay, clean non-toolchain source reproduction, and rebuilt-artifact replay as separate runs/statuses. A checker exit 0 supplies only the replay result for its resolved artifacts; it does not establish a source rebuild, rule out extra endpoint axioms, or establish manuscript faithfulness. Retaining imported toolchain artifacts and replaying their safe logical declarations are compatible and should both be stated.
