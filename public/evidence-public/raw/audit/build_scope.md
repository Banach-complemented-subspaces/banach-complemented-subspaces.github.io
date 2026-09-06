# Pinned Lake build-target scope

This is a read-only inspection of the installed Lean/Lake 4.34.0-rc2 sources and the project's unchanged `lakefile.toml`. No Lean or Lake command was run to produce this scope analysis.

## Result

`lake --no-cache build +ComplementedSubspace:olean` requests the **module** `ComplementedSubspace` and recursively builds its imports. The local source closure consists of **177 modules**: the root file, 155 files under `ComplementedSubspace/`, and all 21 files under `BanLat/`.

For this particular configuration, that is also the complete module set selected by the configured **default library build**. A bare `lake build`, `lake build ComplementedSubspace`, or `lake build ComplementedSubspace:leanArts` does not expand the set to every source under the library prefix. The library's default glob selects only the root, after which imports are followed. The actual library facet is named `leanArts`, not `leanArtifacts`, and `olean` is a module facet rather than a library facet.

There are **193 existing library-member source files** in total: the root file, all 171 files under `ComplementedSubspace/`, and all 21 under `BanLat/`. Thus **16 additional library modules** are not reached by the configured default build. These are 13 audit modules and three other modules. Building the default library facet again would not compile these additional modules.

To verify every existing module belonging to either configured library without changing configuration or mathematical source, follow the successful root-closure build with one sequential `lake --no-cache build` invocation containing all 16 explicit `+Module:olean` arguments stored in the `extra_olean_targets` array in `build_scope.json`.

Do not substitute a bare `BanLat` library build as a means of compiling its directory: its default root is `BanLat`, but there is **no `BanLat.lean` file**. Its 21 existing submodules are already in the root import closure.

## Exact omitted modules

All paths below are relative to `ComplementedSubspace/`:

| File | Explicit module build argument |
|---|---|
| `ComplexCorollaryAudit.lean` | `+ComplementedSubspace.ComplexCorollaryAudit:olean` |
| `ComplexRealDPRAudit.lean` | `+ComplementedSubspace.ComplexRealDPRAudit:olean` |
| `FiniteHilbertWitnessAudit.lean` | `+ComplementedSubspace.FiniteHilbertWitnessAudit:olean` |
| `FiniteOverlapScaleAudit.lean` | `+ComplementedSubspace.FiniteOverlapScaleAudit:olean` |
| `FiniteParameterAudit.lean` | `+ComplementedSubspace.FiniteParameterAudit:olean` |
| `LocalHilbertAudit.lean` | `+ComplementedSubspace.LocalHilbertAudit:olean` |
| `LocalHilbertDualTopAudit.lean` | `+ComplementedSubspace.LocalHilbertDualTopAudit:olean` |
| `LocalHilbertQuotientAudit.lean` | `+ComplementedSubspace.LocalHilbertQuotientAudit:olean` |
| `LocalHilbertRecursiveQuotient.lean` | `+ComplementedSubspace.LocalHilbertRecursiveQuotient:olean` |
| `ProductFrameTranspose.lean` | `+ComplementedSubspace.ProductFrameTranspose:olean` |
| `ProjectionAssemblyAudit.lean` | `+ComplementedSubspace.ProjectionAssemblyAudit:olean` |
| `PureFrameDPRAudit.lean` | `+ComplementedSubspace.PureFrameDPRAudit:olean` |
| `RealMainAudit.lean` | `+ComplementedSubspace.RealMainAudit:olean` |
| `RealMainConsequencesAudit.lean` | `+ComplementedSubspace.RealMainConsequencesAudit:olean` |
| `RecursiveParametersAudit.lean` | `+ComplementedSubspace.RecursiveParametersAudit:olean` |
| `SelectedFrameBasis.lean` | `+ComplementedSubspace.SelectedFrameBasis:olean` |

The other 35 top-level audit/review `.lean` files and the two `experiments/unverified/` files are outside the module prefixes of the two declared libraries. They should be described separately from the configured library build; a claim that every `.lean` file anywhere in the workspace compiled would additionally need direct checks of those files. Current audit-only files under `verification/independent-audit-2026-09-05/` are also outside those library prefixes.

## Local pinned source evidence

The following references are relative to the pinned runtime's source directory:

`WORKSPACE/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean/`

| Source | Mechanism |
|---|---|
| `lake/Lake/CLI/Build.lean:172` (`resolveTargetBaseSpec`), especially `:178` | A leading `+` selects `ws.findTargetModule?` followed by `resolveModuleTarget`, bypassing the library target with the same name. |
| `lake/Lake/CLI/Build.lean:70` (`resolveModuleTarget`) | Resolves the requested module facet; an unspecified module facet is `leanArts`. |
| `lake/Lake/CLI/Build.lean:89` (`resolveConfigDeclTarget`) | A declared target without a specified facet selects its `default` facet. |
| `lake/Lake/CLI/Build.lean:115` (`resolveDefaultPackageTarget`) | The package's `defaultTargets` are resolved as configured targets. |
| Project `lakefile.toml:4` | The only package default target is `ComplementedSubspace`. Both declared libraries omit `roots`, `globs`, and `defaultFacets` overrides. |
| `lake/Lake/Config/LeanLibConfig.lean:36` | Library roots default to `#[name]`; submodules of roots belong to the library. |
| `lake/Lake/Config/LeanLibConfig.lean:46` | The files selected to build default to `roots.map Glob.one`, not a recursive directory glob. |
| `lake/Lake/Config/LeanLibConfig.lean:88` | Library `defaultFacets` default to `#[LeanLib.leanArtsFacet]`. |
| `lake/Lake/Config/LeanLibConfig.lean:128` | `isBuildableModule` accepts the extra root-prefixed module targets because the root itself is globbed, even though these modules are not automatically selected by the default build. |
| `lake/Lake/Config/Glob.lean:53` | `Glob.one` enumerates only its named module; the separate `submodules` and `andSubmodules` cases recurse through directories. |
| `lake/Lake/Config/Module.lean:62` | `LeanLib.getModuleArray` enumerates the configured `globs`. |
| `lake/Lake/Build/Library.lean:36` | `recCollectLocalModules` starts from that module array and follows local imports belonging to the same library. Other-library imports are built by the module dependency pipeline. |
| `lake/Lake/Build/Library.lean:67` | `recBuildLean` requests `mod.leanArts` for the collected modules. |
| `lake/Lake/Build/Library.lean:177` | `recBuildDefaultFacets` delegates to the configured facets. |
| `lake/Lake/Build/Module.lean:1132` and `:1148` | The `olean` module facet fetches `mod.leanArts` and projects its `.olean` artifact. It does not discover sibling source modules. |
| `lake/Lake/CLI/Help.lean:134` | The installed help distinguishes library `leanArts` from module `olean` and documents the `+` module disambiguator. |

The source counts and exact extra module list were computed by breadth-first traversal of the comment-aware import inventory in `placeholder_scan.json`, starting from `ComplementedSubspace`. The independently scanned filesystem inventory supplied the full library-member set. `build_scope.json` preserves the complete 177-name closure, all 16 omitted module records and source hashes, and the ready-to-use extra target argument array. This scope analysis is not a substitute for the recorded compiler exit statuses of those commands.
