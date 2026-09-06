# Independent Lean audit evidence

Final result: PASS

Read `audit-evidence/verification_report.md` for the final findings and limits. This
archive contains 233 original Lean/configuration files under
`audited-source/` and 70 evidence files under `audit-evidence/`.
The source paths are preserved. Mathematical source bytes match both the before
and after audit snapshots. This is a mechanical Lean audit, with no claim of
faithfulness to a manuscript.

## Integrity

`SHA256SUMS.txt` lists every other ZIP member, including this README. Its own hash
is intentionally omitted because a manifest cannot contain its own final hash.
Packaging verified every member against that manifest and checked all ZIP CRCs.
The archive's size and SHA-256 are in the separately delivered
`packaging_result.json`; that file is excluded from the archive to avoid recursion.

## Reproduce

1. Extract to a fresh directory. Treat `audited-source/` as the project root.
   Preserve `audit-evidence/` untouched. Copy its audit scripts (`.lean`, `.ps1`,
   `.py`) and `build_scope.json` to a new
   `audited-source/verification/independent-audit-2026-09-05/` directory. Keep
   the supplied output/status files separately: the runners produce fresh
   evidence, and the supplemental runner requires no existing supplemental status.
2. Install the exact toolchain `leanprover/lean4:v4.34.0-rc2`. The recorded compiler was Lean
   4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`; compiler and Lake
   executable hashes and versions are in `environment.txt`.
3. Restore/check out each external dependency at the commit in the unchanged
   `lake-manifest.json`. The toolchain and external dependency trees/caches are
   not bundled. Matching dependency build caches may be restored, or dependencies
   may be built from these pinned sources. `dependency_provenance.txt` records the
   actual local dependency checkout state used in the recorded audit.
4. In the copied audit scripts, adjust machine-specific runtime/provenance paths
   to your installation. `run_independent_audit.ps1` and
   `run_additional_modules.ps1` need the Lean/Lake runtime path;
   `TraceDependencies.lean` has an explicit `outputDirectory` string;
   `placeholder_scan.py` locates the pinned Lean source distribution for option
   evidence; provenance/source-map helpers retain the original workspace and
   archive paths. Change these audit-only path settings, keeping the original
   mathematical sources and three pinned configuration files unchanged.
5. From the reconstructed project root, run the core and supplemental compiler
   runners sequentially, then refresh the source scan (Python 3.12+ and `rg` are
   needed). The copied audit directory is the output directory:

   ```powershell
   & './verification/independent-audit-2026-09-05/run_independent_audit.ps1'
   & './verification/independent-audit-2026-09-05/run_additional_modules.ps1'
   & '<python.exe>' './verification/independent-audit-2026-09-05/placeholder_scan.py'
   ```

   Inspect each command's exit code and the emitted status files/logs. The core
   runner rebuilds the project, checks the theorem and exact definitions, audits
   axioms, and traverses the declaration graph. The additional runner checks the
   present library modules outside the root import closure. For exact commands,
   flags and ordering, see those scripts and their recorded logs. Regenerate the
   provenance/source maps and final report to describe your own run before
   repackaging; a prior report is evidence of the recorded run only.

## Meaning of the recorded clean rebuild

The core run removed the root package's `.lake/build` outputs, including vendored
BanLat outputs, and checked that no root `.olean` remained before rebuilding.
The external packages under `.lake/packages` and their existing dependency build
caches were retained. `lake --no-cache` disabled Lake artifact-cache lookup for
the invoked commands. This audit did not rebuild all external dependencies from
scratch. `clean_state.txt`, `clean.log`, `build.log`, the supplemental build logs,
and both run-status files document the actual scope.

## Pinned external dependencies

- plausible: `d9598f07b1bc701f1e3aae163d2681c1fd978793` from https://github.com/leanprover-community/plausible
- LeanSearchClient: `ba67e212be1197b84c1f1f6299488a10a3002713` from https://github.com/leanprover-community/LeanSearchClient
- importGraph: `1681d78dd6e65e38b143f9740d829c826673807c` from https://github.com/leanprover-community/import-graph
- proofwidgets: `a8acbfd87375ff4abe14ce09db5b7664d383bc7f` from https://github.com/leanprover-community/ProofWidgets4
- aesop: `18889deb9e83ea7420ef51c160d6f88552e744e3` from https://github.com/leanprover-community/aesop
- Qq: `507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3` from https://github.com/leanprover-community/quote4
- batteries: `4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb` from https://github.com/leanprover-community/batteries
- Cli: `ab3a82db9fea14cf0fd7f5a2de650f4b534640af` from https://github.com/leanprover/lean4-cli
- mathlib: `4cbb42e75a050e830b7cf0f2ae748d7644f59cf7` from https://github.com/leanprover-community/mathlib4.git

## Packaging exclusions

- No packaging outputs or bytecode caches were present.

The package builder is included as `audit-evidence/package_audit.py`. It requires
both compiler status files to pass, an explicit `Final result: PASS` in the final
report, matching before/after/current original sources, and a current passing
source scanner inventory. It creates no mathematical proof or assumption.
