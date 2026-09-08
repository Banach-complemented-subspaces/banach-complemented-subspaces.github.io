# Reproducing the full fresh Lean audit

This is a reproduction procedure, not a record of a completed run. Consult the packaged final report and each native command record for actual outcomes. It was prepared from `evidence/audit_runner.py`, `evidence/prepare_reproduction.py`, and `evidence/rebuild_and_replay.py` for the audit begun on 2026-09-06. Those original runners contain Windows paths and a fixed deadline; retain them as evidence rather than executing them unchanged on another machine.

## Inputs and scope

Use the frozen mathematical project, its unchanged `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`, the exact dependency sources, and the pinned Lean distribution. Do not update dependencies or modify mathematical statements, proofs, or configuration to obtain a passing run.

The target is the complete imported environment of module `ComplementedSubspace`. The clean source build covers its non-toolchain import closure. It does not claim to build unrelated Mathlib modules, every unused project file, or Lean itself. The subsequent official fresh replay separately checks imported logical declarations, including the safe logical declarations from the retained toolchain. See the replay limitations below.

The evidence bundle supplies `source/frozen-project-source.zip` and `source/dependency-sources.zip`. The latter has `<package>/<tracked path>` entries, with all 10,056 recorded tracked dependency files and no dependency `.git` directories or old compiled Lean artifacts. Use the bundle's final hash manifest to verify the archive bytes; these hashes are not an external signature. The separately preserved BanLat licence and porting notes are in `evidence/BanLat-LICENSE` and `evidence/BanLat-PORTING.md`; retain them with extracted BanLat source. **Extraction and rebuilding solely from these distributable archives was not the method used by the recorded local audit**: its dependency trees were independent byte copies of the existing pinned checkouts, including standalone `.git` directories. The archive route below requires real pinned checkouts to supply repository metadata.

Project identity is specified by `evidence/source-manifest-before.sha256`: 233 mathematical/configuration files, including 230 Lean files. Its recorded SHA-256 is:

```text
875e2219bcfe9ea3c6a66a21fecbb077fc225b47e4ab39a0720f82735fe8fa3a
```

Dependency identity is specified by `evidence/dependency-source-manifest-before.sha256`, with paths relative to `.lake/packages/`. `evidence/dependency-revisions.json` records the original revision and tracked file inventory for each dependency. Source hashes, not merely Git revision labels, must match before and after all checks. Preserve `BanLat/PORTING.md` and the BanLat licence: the frozen 21-module vendored subset is based on [BanLat commit 5c9360ccd9cef27b749f3cabda6348fd2529d1a3](https://github.com/davidmunozlahoz/banlat/tree/5c9360ccd9cef27b749f3cabda6348fd2529d1a3), with the recorded import compatibility changes already included in the frozen project.

## Toolchain and dependency pins

Use Lean `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`, and its bundled Lake `5.0.0-src+6a10ac8`. The toolchain name is `leanprover/lean4:v4.34.0-rc2`. Obtain a platform-appropriate distribution explicitly before the audit if it is not already installed; this procedure does not require a script to download it. [Official Lean release](https://github.com/leanprover/lean4/releases/tag/v4.34.0-rc2).

The following are the recorded Windows executable SHA-256 values. Other platforms' binaries will differ; record their release provenance and actual hashes instead of asserting binary identity with Windows.

| Executable | SHA-256 |
|---|---|
| `lean.exe` | `37dfe799f69b990251f3b6bcff8a1c10c1afe2adcdecc5c580cc6726ffb63433` |
| `lake.exe` | `5afaf2ad866c1aa6c1eda7bdb84ebd99e1de8be3a95a219094654dfa00b47c0a` |
| `leanchecker.exe` | `b7c503a7a984f32f04c1badb79e53e350ddb72aed530da12699e4b06357ce149` |

| Directory under `.lake/packages/` | Public repository | Exact revision |
|---|---|---|
| `mathlib` | https://github.com/leanprover-community/mathlib4.git | `4cbb42e75a050e830b7cf0f2ae748d7644f59cf7` |
| `plausible` | https://github.com/leanprover-community/plausible | `d9598f07b1bc701f1e3aae163d2681c1fd978793` |
| `LeanSearchClient` | https://github.com/leanprover-community/LeanSearchClient | `ba67e212be1197b84c1f1f6299488a10a3002713` |
| `importGraph` | https://github.com/leanprover-community/import-graph | `1681d78dd6e65e38b143f9740d829c826673807c` |
| `proofwidgets` | https://github.com/leanprover-community/ProofWidgets4 | `a8acbfd87375ff4abe14ce09db5b7664d383bc7f` |
| `aesop` | https://github.com/leanprover-community/aesop | `18889deb9e83ea7420ef51c160d6f88552e744e3` |
| `Qq` | https://github.com/leanprover-community/quote4 | `507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3` |
| `batteries` | https://github.com/leanprover-community/batteries | `4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb` |
| `Cli` | https://github.com/leanprover/lean4-cli | `ab3a82db9fea14cf0fd7f5a2de650f4b534640af` |

## Prepare a new isolated directory

Choose three absolute paths: a previously nonexistent reproduction directory `REPRO`, a previously nonexistent result directory `RESULTS`, and an initially nonexistent private cache directory `CACHE`. Keep them separate from the original project, previous audit evidence, and the toolchain. Refuse to overwrite or empty any existing reproduction, evidence, or cache directory. Preserve the supplied evidence read-only. Choose an explicit new UTC computation deadline, with additional time reserved for saving evidence.

Extract the frozen project into `REPRO`, preserving its relative paths and exact bytes. Supply all nine dependency repositories at `REPRO/.lake/packages/<name>` by one of these methods:

1. Copy already available pinned checkouts using ordinary independent file copies, excluding `.lake`, `.cache`, and `node_modules`. Retain standalone `.git` metadata. Do not use hard links, symlinks, junctions, Git worktrees, shared object stores, or object alternates. This is the method used by the recorded local audit.
2. As an explicit preparatory network action, obtain the public repositories above and check out their exact revisions. For each row, the command pattern is `git clone --no-checkout <repository> <new-package-directory>`, followed by `git -C <package-directory> checkout --detach <revision>`. These commands download public sources and must be a deliberate user action, before the isolated build. Ensure checkout line-ending/filter settings reproduce the recorded bytes. If hashes differ, stop and investigate; do not normalize or edit files silently. The supplied dependency source archive provides the exact recorded bytes for comparison/restoration within the new checkouts. Record any restoration and confirm all manifest hashes afterward; do not invent revision metadata with `git init` or a manufactured commit.

For each dependency record native `git rev-parse HEAD`, `git status --porcelain=v1 --untracked-files=normal`, and `git ls-files -z`. Verify that HEAD matches the manifest, that the tracked set is exactly the recorded set, and that each tracked file has the expected SHA-256. The recorded original checkouts were clean. Review and document any discrepancy before continuing.

Scan the new tree, excluding `.git`, for preexisting `.olean`, `.ilean`, `.ir`, `.o`, `.obj`, `.a`, `.dll`, `.so`, and `.dylib` files: there must be none. Confirm project/dependency `.lake/build` directories are absent and that there are no reparse points, symlinks, junctions, `.git/commondir`, or `.git/objects/info/alternates`. Resolve all paths to establish that builds cannot reach original outputs. Do not clean an original tree to achieve these conditions: choose a new independent copy.

Preserve ProofWidgets' canonical tracked JavaScript files and their tracked `lake.trace`/package-lock trace inputs exactly. They are pinned non-Lean source inputs for this procedure; this audit does not claim to rebuild their TypeScript. Do not globally remove every `.trace` file. Missing or stale frontend inputs can trigger package prerequisites, including npm activity; investigate such a failure rather than changing package configuration or permitting an unrecorded download.

To verify a manifest portably, the following read-only Python pattern is sufficient after setting `BASE` and `MANIFEST` to the appropriate paths. Use it for the original/frozen inputs, the reproduction, and the dependencies, both before and after execution. Retain the output and actual exit code.

```python
from pathlib import Path
import hashlib
BASE = Path("<absolute source base>")
MANIFEST = Path("<absolute manifest path>")
base = BASE.resolve(strict=True)
count = 0
for line in MANIFEST.read_text(encoding="utf-8").splitlines():
    expected, relative = line.split("  ", 1)
    file = (base / relative).resolve(strict=True)
    if not file.is_relative_to(base) or not file.is_file():
        raise RuntimeError(f"Invalid manifest path: {relative}")
    actual = hashlib.sha256(file.read_bytes()).hexdigest()
    if actual != expected:
        raise RuntimeError(f"Source hash mismatch: {relative}")
    count += 1
print(f"PASS: {count} file hashes match")
```

This hash loop does not replace the independent tracked-set and symlink checks. Python 3.9 or later is required for `Path.is_relative_to`.

## Child environment and cache controls

Use absolute paths to the pinned `lake`, `lean`, and `leanchecker` executables, and prepend the pinned `bin` directory to the child PATH. Remove inherited `LEAN_PATH`, `LEAN_SRC_PATH`, `LEAN_SYSROOT`, `LAKE_HOME`, and `LAKE_PACKAGES_DIR`. Inspect any other toolchain, Git URL, native library, or path override that could redirect resolution. Record only relevant environment values, not credentials.

The recorded source-build runner used these exact additional values:

```text
LAKE_ARTIFACT_CACHE=false
LAKE_RESTORE_ARTIFACTS=false
LAKE_CACHE_DIR=<CACHE>
MATHLIB_NO_CACHE_ON_UPDATE=1
LEAN_NUM_THREADS=4
```

Every source-build and rebuilt-replay command also uses `--no-cache`. This disables automatic package build-cache downloads. `LAKE_ARTIFACT_CACHE=false` separately disables local artifact-cache reads; the private initially empty cache and initially absent build outputs exclude previous local outputs. `LAKE_RESTORE_ARTIFACTS=false` is a default, not an override of Mathlib's explicit `restoreAllArtifacts := true`; do not attribute isolation to that environment variable alone. `MATHLIB_NO_CACHE_ON_UPDATE=1` is a defensive guard, not permission to update. Do not run `lake update`, `lake cache get`, `lake exe cache get`, unpack targets, or release-cache download targets.

These controls are not a network sandbox. Have all source repositories, native prerequisites, and canonical tracked frontend inputs available first. An unexpected dependency fetch or package hook should be recorded and investigated; the audit must not silently install anything. `LEAN_NUM_THREADS=4` is the recorded setting, not a demonstrated universal process-count or total-memory cap. The frozen project retains its own `-j1` and `-M8192` weak Lean arguments; do not claim they constrain all dependency subprocesses.

## Exact native commands and stage order

In the examples, `<LAKE>`, `<LEAN>`, and `<CHECKER>` are absolute pinned executable paths, `<PYTHON>` is an available Python executable, and `<BUNDLE>` is the read-only extracted evidence bundle. Angle-bracket values are placeholders, not literal shell syntax. Run executable/argument vectors without a shell where possible. The original audit's authoritative argument vectors, working directories, raw output paths, timings, relevant environment, and native exit codes are in its `*.command.json` files.

First record `<LEAN> --version` and `<LAKE> --version`, executable/source hashes, platform details, pins, and all pre-run source hashes. `leanchecker` has no supported help/version interface in this pinned release; do not treat `leanchecker --help` as a harmless version probe.

If the original built artifacts are available, preserve a separate initial-artifact replay with its own record, from the original project directory:

```text
<LAKE> env <CHECKER> --fresh --verbose ComplementedSubspace
```

The recorded original root artifact had SHA-256 `b0874218a920926d711a7949ba0ba48f1d3a0014da86c399e3dfb1eedbb15ee7`. A source-only recipient cannot claim to repeat that exact historical-artifact stage. Do not manufacture that stage by relabeling a replay of newly built outputs; mark it unavailable and retain the original recorded evidence.

Before the clean build, inspect Lake's resolved child environment from `REPRO`:

```text
<LAKE> --no-cache env <PYTHON> -c "import os; print('\n'.join(k+'='+v for k,v in os.environ.items() if k.startswith(('LEAN','LAKE','MATHLIB'))))"
```

Verify that non-toolchain Lean library/module paths resolve only inside `REPRO`; the intentionally retained pinned toolchain paths are allowed. Check actual paths, not only whether a particular spelling of the original directory appears. Save this output, then run from `REPRO`:

```text
<LAKE> --no-cache build +ComplementedSubspace:olean
```

Continue only after native exit code 0 and the presence of the new `REPRO/.lake/build/lib/lean/ComplementedSubspace.olean`. Inventory and hash actual newly produced primary `.olean` files by module/package, along with available build/setup evidence. Do not equate aggregate Lake job counts with compiled-module counts or with replayed-declaration counts. Recheck resolved paths after the build, then run from `REPRO`:

```text
<LAKE> --no-cache env <CHECKER> --fresh --verbose ComplementedSubspace
```

Preserve the rebuilt root artifact hash and the replay's raw streams and native exit code. Run the supplied endpoint/definition helpers against this same reproduction environment:

```text
<LAKE> --no-cache env <LEAN> -j1 -M8192 <BUNDLE>/evidence/EndpointChecks.lean
<LAKE> --no-cache env <LEAN> -j1 -M8192 <BUNDLE>/evidence/PrintDefinitions.lean
<LAKE> --no-cache env <LEAN> -j1 -M8192 <REPRO>/MainTheoremReview.lean
```

The five endpoints are `ComplementedSubspace.realMainTheorem`, `ComplementedSubspace.realCorollary`, `ComplementedSubspace.realUnconditionalCorollary`, `ComplementedSubspace.realSeparableNonprimarity`, and `ComplementedSubspace.complexCorollary`. Check their exact types, statement-definition bodies, implicit variable context, and formulation identity against the frozen source. Inspect each actual `#print axioms` result: its set must be a subset of `{propext, Classical.choice, Quot.sound}`, with no `sorryAx` or added axiom. A successful process that merely printed a disallowed axiom is not a successful axiom audit.

Repeat all project/configuration and tracked dependency hash/set checks on both the original inputs and the new reproduction. Retain the supplementary lexical source scan and all findings separately from kernel replay. The original `check_identity_and_scan.py` also checks machine-specific website paths; adapt only an audit-local copy's path constants for a different environment, document that adaptation, and never modify the frozen sources. Source scanning and declaration-axiom traversal do not replace official replay or a mathematical correspondence review.

## Recording and deadline policy

For every native command create a unique new record before launching it. Refuse existing record or output names. Record the executable and argument vector, cwd, relevant environment, start/end UTC, elapsed time, native exit code, and any timeout/launch error. Capture stdout and stderr directly to separate binary files to preserve the original bytes. A combined display log may concatenate those streams with labels; it is not a chronological interleaving. Preserve failed attempts, helper errors, and timeouts without replacing their records.

Use the selected wall-clock deadline in an audit-only runner. On expiry, stop only the process tree started by that runner, retain the actual resulting native exit code and the stop outcome, and mark the stage `NOT COMPLETED`. Never kill unrelated Lean processes or report a timeout as PASS. The historical Windows runner used its own recorded PID with `taskkill /T /F`; a portable runner must use the corresponding owned-process-group mechanism on its platform. Merely abandoning a waiting Python process is insufficient if child compilers continue running.

An audit PASS requires each claimed stage to have actually completed and all identity/axiom checks to pass. An incomplete source build or replay remains `NOT COMPLETED`, even if earlier stages passed. Keep the final status, exact command records, raw streams, clean-state/path/cache evidence, manifests, dependency revisions, helper sources, artifact inventory, and all failures together in the new result directory.

## What official fresh replay establishes

In the pinned [LeanChecker.lean](https://github.com/leanprover/lean4/blob/6a10ac8c22beadecabdbb0919c2b50214762f91d/src/LeanChecker.lean), `--fresh` imports the target and replays its imported constants into an empty kernel environment using [Lean/Replay.lean](https://github.com/leanprover/lean4/blob/6a10ac8c22beadecabdbb0919c2b50214762f91d/src/Lean/Replay.lean). There is no blanket core/standard-library package exclusion from that logical replay. Dependencies are replayed recursively, and safe kernel declarations are submitted to the kernel at trust level 0. Unsafe and partial declarations are skipped by the official implementation. Constructors/recursors are checked against regenerated declarations, and quotient support follows Lean's primitive rules. Axioms remain assumptions, so the separate endpoint axiom allowlist matters.

`--verbose` prints the replay target/mode, not a per-declaration progress/count certificate. Native exit code 0 is the completion evidence; do not invent declaration counts from that output. This is a fresh replay through the pinned Lean kernel, not a second independent kernel implementation, a fresh compiler bootstrap, or proof that the formal statements perfectly match the manuscript. The [official Validating Proofs reference](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) explains the broader trust boundary; the pinned local implementation takes precedence where latest documentation names a different checker or interface. The retained toolchain and the structural loading of compiled files remain part of the stated computational trust boundary.

The accompanying `checker-provenance-and-scope.md` and `rebuild-controls.md` contain detailed pinned-source references. No additional automated reproducer is supplied here: the preserved runners document the actual run, while the portable commands above avoid pretending that their original paths, dated deadline, or website-specific identity checks work unchanged elsewhere.
