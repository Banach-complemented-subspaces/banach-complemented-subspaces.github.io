# Final fresh Lean audit status — 6 September 2026

All requested mathematical checks passed. Final packaging status: **PASS**.

| Stage | Result |
|---|---|
| 1. Source/environment/target identity | PASS |
| 2. Existing-artifact fresh replay | PASS — exit 0, 598.000 s |
| 3. Imported-dependency and project source reproduction | PASS — exit 0, 6,896.594 s |
| 4. Rebuilt-artifact fresh replay | PASS — exit 0, 833.828 s |
| 5. Endpoint types, definition identity, axioms | PASS — all native exit codes 0 |
| 6. Final source preservation and packaging | See packaging result above and archive-validation.json |

Both replay invocations used the pinned `lake.exe` and `leanchecker.exe`: `lake env leanchecker --fresh --verbose ComplementedSubspace` in the original project and `lake --no-cache env leanchecker --fresh --verbose ComplementedSubspace` in the reproduction. The source command was `lake --no-cache build +ComplementedSubspace:olean`.

Actual rebuilt coverage: 2,774 primary modules = 177 project/BanLat/root plus 2,597 external modules, including 2,340 Mathlib modules. No precompiled non-toolchain Lean artifacts were reused or fetched. The pinned Lean toolchain and tracked ProofWidgets JavaScript inputs were retained.

Exact endpoints: `ComplementedSubspace.realMainTheorem`, `ComplementedSubspace.realCorollary`, `ComplementedSubspace.realUnconditionalCorollary`, `ComplementedSubspace.realSeparableNonprimarity`, `ComplementedSubspace.complexCorollary`. All five are proved closed declarations at the frozen statement types. Each has exactly `propext`, `Classical.choice`, `Quot.sound`; no additional axiom. The namespace allowlist check covered 2,573 declarations. Source findings include documented external placeholder-generating tactic tools; none introduces an extra axiom dependency into these endpoints.

Lean `4.34.0-rc2` / commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`; Lake `5.0.0-src+6a10ac8`; Mathlib `4cbb42e75a050e830b7cf0f2ae748d7644f59cf7`; BanLat `5c9360ccd9cef27b749f3cabda6348fd2529d1a3`. All nine dependency pins and tracked source bytes are recorded in the report. Each original/reproduced project tree's 233 files and dependency tree's 10,056 tracked files remained unchanged.

Frozen source manifest SHA-256: `875e2219bcfe9ea3c6a66a21fecbb077fc225b47e4ab39a0720f82735fe8fa3a`. Start 10:28:54 UTC; archive-validation.json records the exact final elapsed time and archive digest. No mathematical audit stage remains unfinished after the packaging PASS.

Report: evidence/report.md (also report.html). Raw logs: evidence/*.log and *.command.json. Download bundle: full-fresh-audit-evidence.zip, with internal CONTENTS.sha256 and detached archive-validation.json. Reproduction: evidence/REPRODUCE.md.

Companion location: existing Verification page, `/verification/#extended-fresh-audit`. Website integration/validation is recorded separately after the mathematical audit package is finalized. Everything remains local and unpublished; no uploads or power-setting/shutdown actions occurred. Raw local evidence retains personal Windows paths for review before any eventual public release.
