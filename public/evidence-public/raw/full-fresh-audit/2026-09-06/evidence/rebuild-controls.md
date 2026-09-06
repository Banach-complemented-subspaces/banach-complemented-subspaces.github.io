# Pinned Lake source-rebuild controls

Research scope: read the full `USER_HOME/Downloads/CODEX_FULL_FRESH_LEAN_AUDIT_AND_WEBSITE (1).txt`, the original project configuration and dependency manifests, and the installed pinned Lake/Lean source and CLI help. No compilation, build, cleanup, dependency update, source edit, or archive modification was performed for this research. This note describes controls; it is not a certificate that the fresh source rebuild or its subsequent replay has completed.

Original project: `LEAN_PROJECT`.

Pinned runtime: `WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows`. The inspected tools report Lean `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`, and Lake `5.0.0-src+6a10ac8`. Source references below are relative to this runtime's `src/lean/` directory unless a dependency source is named. `lake --help`, `lake help build`, `lake help env`, and `lean --help` were read successfully with exit code 0.

## Command and child-process environment

From the independently copied reproduction workspace, the supported root build command is:

```powershell
& 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' --no-cache build '+ComplementedSubspace:olean'
```

Lake also supports `--rehash`, `--verbose`, and `--no-ansi`; `--rehash` makes file hashing independent of saved `.hash` metadata. These are optional diagnostic additions to the supported command, not a claim that the running command includes them. The parent reports that its actual source build uses the command above. Record that actual command and its output, exit code, working directory, and environment in the run evidence.

Set the following in the isolated build's child environment:

```text
LEAN_NUM_THREADS=4
LAKE_NO_CACHE=true
LAKE_ARTIFACT_CACHE=false
LAKE_RESTORE_ARTIFACTS=false
LAKE_CACHE_DIR=<an initially empty directory owned by the reproduction>
MATHLIB_NO_CACHE_ON_UPDATE=1
```

Use the absolute pinned Lake executable and the pinned `bin` directory on the child PATH. Clear inherited `LEAN_PATH` and `LEAN_SRC_PATH` before Lake constructs the workspace paths. Inspect inherited toolchain and path overrides, including `LEAN_SYSROOT`, `LAKE`, `LAKE_HOME`, `LEAN_GITHASH`, `ELAN_TOOLCHAIN`, and `LAKE_PKG_URL_MAP`; they must not redirect the runtime, package sources, or artifacts outside the reproduction and the intentionally retained pinned toolchain. Preserve necessary operating-system and native compiler tools on PATH, but remove original-workspace build/library directories. Also inspect native shared-library search paths. Do not emit credentials or unrelated environment secrets when recording the effective environment.

`lake env` adds workspace search paths to inherited paths; it does not establish isolation by itself. `lake/Lake/Config/Env.lean:186` captures inherited paths, and `lake/Lake/Config/Workspace.lean:391` appends them to workspace paths. Inspect generated module setup/import artifact paths as further evidence that non-toolchain inputs resolve only inside the reproduction. `lake env` may load/elaborate configuration, so any such checks belong in the reproduction, not the frozen original.

## Concurrency and memory: supported facts and limitation

The inspected Lake CLI does **not** offer a `-j` or `--jobs` build option. Its short-option parser is in `lake/Lake/CLI/Main.lean:211`; passing Lean's `-j` or `-M` directly as Lake options is unsupported. Lean itself supports `-j`/`--threads` and `-M`/`--memory` (MB); `-T` limits allocation/heartbeat work, not wall-clock time. No trust-level change is part of this plan.

The original project's two library configurations retain `weakLeanArgs = ["-j1", "-M8192"]`. These flags apply to those project libraries; they are not automatically inherited by every external dependency library. `lake/Lake/Config/LeanLib.lean:198` composes package/library arguments, and `lake/Lake/Build/Module.lean:981` passes those arguments to the actual Lean compiler.

This research did **not** establish from pinned runtime implementation that `LEAN_NUM_THREADS=4` is a hard bound on all concurrently executing Lake subprocesses, nor that it enforces a total process-tree memory cap. The distribution lacks the relevant runtime C++ sources; an attempted remote source read did not supply usable confirmation before the research was stopped. No universal `LEAN_OPTS` or unsupported Lake jobs switch is proposed.

At handoff the parent reports that the clean build is running with `LEAN_NUM_THREADS=4` and **exactly four observed Lean compiler processes**. That is measured runtime evidence, not proof of a hard scheduler bound. Continue recording process counts and total process-tree memory; use the parent's bounded execution/termination mechanism for the overall time and resource budget. Do not claim that project `-M8192` caps total memory or applies to all Mathlib compiler processes.

## Cache controls are separate layers

1. `--no-cache` (or `LAKE_NO_CACHE=true`) disables automatic package build-cache downloads. `lake/Lake/Build/Package.lean:48` checks `getTryCache` before fetching GitHub release or Reservoir package artifacts; `lake/Lake/Config/Monad.lean:228` computes it from the no-cache flag. This does not justify invoking explicit cache-fetch targets or executables.
2. `LAKE_ARTIFACT_CACHE=false` separately disables ordinary local artifact-cache reads. Local artifact reads are otherwise enabled by default even when writes are disabled. See `lake/Lake/Config/Monad.lean:180` and `lake/Lake/Config/PackageConfig.lean:270`. An explicit package artifact-cache setting can override the workspace/environment value; the active dependency configurations inspected here contain no explicit enablement overriding this control.
3. Use a private, initially empty `LAKE_CACHE_DIR`, and start every copied non-toolchain package with no previous build output. `lake/Lake/Config/Env.lean:193` and `lake/Lake/Config/Workspace.lean:25` select cache locations. A private nonempty path is clearer evidence than assuming an empty environment string eliminates every workspace fallback.
4. Existing up-to-date traces and build outputs can be reused independently of ordinary local cache reads. `lake/Lake/Build/Module.lean:1051` includes existing-artifact and local archive restoration paths. Therefore the fresh reproduction must initially lack non-toolchain compiled outputs, build traces, and artifact archives; no symlink/junction may lead to original outputs or shared caches.

Mathlib's `lakefile.lean:66` explicitly sets `restoreAllArtifacts := true`. Package configuration overrides the workspace/environment default (`lake/Lake/Config/Monad.lean:180`), so **do not claim `LAKE_RESTORE_ARTIFACTS=false` overrides Mathlib**. Initially absent isolated outputs, disabled local artifact-cache reads, disabled automatic downloads, and an empty private cache are the substantive combined controls.

Do not run `lake update`, `lake --update`, `lake cache get`, `lake unpack`, `lake exe cache get`, or explicit cache/release download facets in the source-rebuild stage. `lake help build` says that a build does not update package dependencies. Mathlib's `post_update` hook (`mathlib/lakefile.lean:177`) invokes its cache executable unless `MATHLIB_NO_CACHE_ON_UPDATE=1`; the environment guard is defense in depth, not permission to update. `lake/Lake/Load/Resolve.lean:538` runs post-update hooks during update/materialization. The inspected parser also recognizes `--offline`, but its complete scope was not verified here, so this plan does not rely on it.

## Source paths, revisions, and isolation checks

The original root manifest uses `packagesDir = ".lake/packages"`; all nine active dependencies have type `git`, with no manifest `subDir`. Their original absolute source paths are the original project path above followed by `/.lake/packages/<name>`. Their default output directories are `<package source>/.lake/build`. These originals must remain read-only during the independent reproduction.

| Package | Manifest revision |
|---|---|
| plausible | `d9598f07b1bc701f1e3aae163d2681c1fd978793` |
| LeanSearchClient | `ba67e212be1197b84c1f1f6299488a10a3002713` |
| importGraph | `1681d78dd6e65e38b143f9740d829c826673807c` |
| proofwidgets | `a8acbfd87375ff4abe14ce09db5b7664d383bc7f` |
| aesop | `18889deb9e83ea7420ef51c160d6f88552e744e3` |
| Qq | `507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3` |
| batteries | `4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb` |
| Cli | `ab3a82db9fea14cf0fd7f5a2de650f4b534640af` |
| mathlib | `4cbb42e75a050e830b7cf0f2ae748d7644f59cf7` |

The root `lakefile.toml` requires Mathlib at that exact revision, defines default target `ComplementedSubspace`, and defines `ComplementedSubspace` and `BanLat` libraries with the unchanged weak Lean arguments stated above. No active top-level dependency configuration inspected here redirects its build directory outside the package. Auxiliary, inactive subprojects do contain relative path dependencies/build overrides, for example `batteries/docs`, `mathlib/DownstreamTest`, and `mathlib/scripts/SideSkimmer`; they must not be mistaken for the active root workspace configuration.

An independent copy must include the pinned tracked source/configuration inputs, with independently writable build directories. Excluding `.lake`, `.cache`, and `node_modules` is appropriate for these copied package inputs, while preserving the tracked ProofWidgets files described below. Inspect directory/file reparse points, `.git` indirection, `commondir`, and object-store alternates before calling the copy independent. A path dependency or junction resolving to the original would invalidate isolation. Preserve original remote URLs and exact revisions if retaining Git metadata: `lake/Lake/Load/Materialize.lean:33` may materialize/check out packages whose repository metadata or revision differs. Do not allow an unexpected materialization/update to silently replace the intended copied sources.

The parent reports that its completed copy contains **10,056 tracked dependency files**, all **nine actual Git revisions match**, all working trees are clean, and the isolated copy initially has **zero compiled artifacts or symlinks**. Those are parent-supplied execution findings; the parent's raw snapshot/copy evidence is authoritative. This research did not repeat a full independent junction/alternate scan after that copy.

## ProofWidgets: preserve canonical tracked non-Lean inputs

The pinned ProofWidgets repository tracks generated `widget/js/*.js`, `widget/js/lake.trace`, `widget/package-lock.json`, and `widget/package-lock.json.trace`. A read-only `git ls-files` inspection confirmed these are tracked inputs. Preserve them exactly. Do not globally delete every `*.trace` file: these canonical tracked traces are distinct from old Lean build-output traces. Untracked generated `.hash` files need not be copied.

Mathlib requires ProofWidgets with an `errorOnBuild` option (`mathlib/lakefile.lean:13`). ProofWidgets' `widgetJsAllTarget` (`proofwidgets/lakefile.lean:54`) checks the traced JavaScript inputs and, if rebuilding is necessary, errors with the supplied message before invoking its normal npm build. Its library has `needs := #[widgetJsAll]` (`:89`). The package-lock target can separately invoke `npm install` when its trace is stale (`:33`). Thus stale/missing canonical traced inputs can block the source rebuild or require native frontend tooling even when Lean outputs are absent.

`+ComplementedSubspace:olean` does not bypass this prerequisite: every module setup awaits library extra dependencies (`lake/Lake/Build/Module.lean:543`; `lake/Lake/Build/Library.lean:164`). CLI `-KerrorOnBuild=` is not a supported way to remove the dependency's option: `-K` sets root configuration options, dependency options are loaded separately, and an empty string remains a present option.

The parent reports that the isolated copy preserved these tracked JS assets and trace inputs. Disclose that the source reproduction retains canonical pinned non-Lean JavaScript assets; do not say their TypeScript was freshly compiled. No workaround is currently anticipated. If this prerequisite actually fails, record its exact failure and treat any configuration-only remedy separately; do not silently skip it or edit mathematical source.

## Exact target and claimed source scope

In `+ComplementedSubspace:olean`, `+` selects a module unambiguously, and `:olean` selects its compiled module facet (`lake help build`). The root source imports the endpoint environment. Module setup recursively fetches imported modules across the workspace and required native/plugin/library prerequisites; see `lake/Lake/Build/Module.lean:543`. The olean facet depends on the module's Lean artifact build (`:1132`), so it is not merely a check of the outer root wrapper and may produce additional C/IR/metadata/native prerequisites.

With all non-toolchain outputs absent and both cache layers disabled, this target is intended to compile the root's imported **non-toolchain dependency closure** from the copied sources. It does not build every unrelated Mathlib file, the whole Lean compiler, every project draft, or every unused audit helper. The pinned toolchain's core/standard-library artifacts are intentionally retained and must be named as such in the final report. The official fresh leanchecker replay is a separate stage and must include the imported declaration environment; neither source compilation alone nor an axiom walker substitutes for it.

Count successful compiled modules from exact module build/invocation evidence, not the number of aggregate Lake jobs. Lake uses distinct `Built`, `Replayed`, `Reused`, `Fetched`, and `Unpacked` job actions (`lake/Lake/Build/Job/Basic.lean:31`). A replayed canonical non-Lean input trace is different from reuse of a non-toolchain Lean artifact. Preserve verbose logs/setup paths and identify any cache/reuse action by the actual artifact/package before claiming source completeness.

At handoff the parent reports that the first official fresh replay passed with exit code 0 after 598 seconds, and the isolated source build is in progress. This note makes no claim about that build's eventual exit code, completion count, rebuilt-artifact replay, or overall FULL FRESH AUDIT result. The brief's separate stage outcomes must remain explicit; an unfinished stage cannot be converted to PASS.
