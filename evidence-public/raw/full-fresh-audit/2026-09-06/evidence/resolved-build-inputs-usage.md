# Resolved setup input checker

Run only after the isolated source build has stopped and its inputs are quiescent. The helper reads the reproduction and pinned toolchain; it writes only a separately chosen new/empty report directory. It invokes no native tools, Lean, Lake, Git, network operations, or cleanup.

Example (the report directory is a new sibling of `reproduction`, not inside it):

```powershell
& 'USER_HOME\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' 'WORKSPACE\tmp\full-fresh-audit-research\check_resolved_build_inputs.py' --output-dir 'WORKSPACE\output\full_fresh_audit_2026-09-06_102854\resolved-build-inputs'
```

Defaults are exactly the requested reproduction and pinned runtime paths; `--reproduction`, `--toolchain`, and `--required-module` allow explicit overrides, which are recorded. The default required root setup is `ComplementedSubspace`; its absence makes the result incomplete so a partial build cannot pass merely because its existing inputs are contained.

- Exit 0 / **PASS**: supported files read, required root setup present, every explicit imported-artifact/plugin/dynamic-library path exists and remains within the two specified roots after Windows path resolution.
- Exit 1 / **FAILED CHECK**: an actual path escape or allowed-root redirection was found, even if other observations are incomplete.
- Exit 2 / **NOT COMPLETED**: missing inputs/setup, unknown format, relative path whose compiler base was not proved, incomplete traversal, unsupported platform, or another observation error. Invalid invocation/output destination also exits 2.

`summary.json` contains the invocation, script hash, counts, status, limits and sidecar hashes. `findings.json` contains full findings. `paths.json` deduplicates raw/resolved path observations. `module_map.jsonl` retains each setup's hash/name/package and every input reference, with IDs joining to `paths.json`. Each complete module record is streamed and flushed as that setup is processed; only that module's references are held in memory. `module_summaries.json` retains small per-module summaries and reference counts. Sidecar SHA256 hashes are computed in 1 MB chunks, without loading the full map. Counts of unique paths include setup files and scanned directories as well as input artifacts; `referenceCounts` reports actual input references separately.

The pinned format was inspected in two actual reproduction files: `Qq/Typ.setup.json` (empty import map) and `Mathlib/Control/ULift.setup.json` (nested imported-artifact arrays). `Lean/Setup.lean:69` defines `ImportArtifacts` as arrays of path arrays; `:143` and `:164` define plugins as a path object or accepted string; `:188` defines the setup fields. The helper handles all entries in these arrays, including optional server/private olean and IR parts, rather than inspecting only one olean per import. Unknown top-level/plugin fields are incomplete so new path-bearing fields are not silently ignored.

This is a path-containment check, not an operating-system trace of compiler reads. Setup files do not necessarily enumerate retained toolchain imports. It does not prove artifact freshness, pins, full compilation, source integrity, or the native loader's transitive dependencies. Keep the separate environment, clean-copy, build, hash and fresh leanchecker evidence. A post-build check cannot retroactively prove paths never changed earlier.

Preparation validation is syntax-only, as requested; the helper has not been run against the active build or audit evidence. No source/configuration files were changed.
