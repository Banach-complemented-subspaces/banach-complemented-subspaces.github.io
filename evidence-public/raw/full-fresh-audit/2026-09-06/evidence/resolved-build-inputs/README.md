# Resolved build input check

Status: **PASS** (exit 0).

Inspected 2774 setup files and 9354642 explicit input references.

`summary.json` records the exact invocation, roots, counts, limits and report hashes. `findings.json` retains every finding. `paths.json` retains raw/resolved paths and containment outcomes. `module_map.jsonl` maps every setup hash/module/reference to path IDs in `paths.json`. `module_summaries.json` contains the small per-module summaries and reference counts.

PASS covers only this path-containment observation; the source-build, source-hash, environment, pin and fresh-replay checks remain separate.
