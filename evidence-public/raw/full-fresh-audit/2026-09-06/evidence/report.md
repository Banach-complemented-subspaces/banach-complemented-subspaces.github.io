# Supplementary full fresh Lean audit — 6 September 2026

**FULL FRESH AUDIT: PASS.** The frozen project and its imported non-toolchain dependencies were rebuilt from pinned sources. Both official fresh kernel replays, all five endpoint checks, definition/source identity, and the transitive axiom allowlist passed. The final archive validation receipt records the completed packaging check.

| Stage | Status | Evidence |
|---|---|---|
| 1. Source/environment identity and target coverage | PASS | [Snapshot](snapshot.json), [source manifest](source-manifest-before.sha256), [pins](dependency-revisions.json), [coverage](coverage.json) |
| 2. Fresh replay of existing frozen artifacts | PASS: exit 0; 598.000 s; 10:33:11–10:43:09 UTC | [Command](initial-fresh-replay.command.json), [raw replay log](initial-fresh-replay.log) |
| 3. Clean source reproduction | PASS: exit 0; 6,896.594 s; 10:45:09–12:40:06 UTC | [Command](source-rebuild.command.json), [raw build log](source-rebuild.log), [clean state](clean-state.json) |
| 4. Fresh replay of rebuilt artifacts | PASS: exit 0; 833.828 s; 12:40:23–12:54:17 UTC | [Command](rebuilt-fresh-replay.command.json), [raw replay log](rebuilt-fresh-replay.log) |
| 5. Endpoint types, definition identity and transitive axioms | PASS: all native exit codes 0; no additional endpoint axioms | [Proof types/axioms](endpoint-types-and-axioms.log), [definitions](printed-mathematical-definitions.log), [formulation identity](review-formulation-identity.log), [source identity](identity-source-and-scan.json) |
| 6. Final source-unchanged checks and evidence packaging | PASS | [Final preservation](final-preservation.json), [final source manifest](source-manifest-after.sha256), [detached archive validation](../archive-validation.json) |

## Snapshot, environment and commands

All timestamps are UTC. The audit began at 10:28:54; computation deadline 13:13:54; evidence handoff deadline 13:28:54. Exact native executable/argument vectors, working directories, relevant environments, timings, raw streams and returned exit codes are preserved in each `*.command.json`. The following path abbreviations expand literally:

```text
W = WORKSPACE
P = W/output/lean_trial_2026-09-05
A = W/output/full_fresh_audit_2026-09-06_102854
R = A/reproduction
E = A/evidence
T = W/tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows
```

The pinned distribution is Lean `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`, with Lake `5.0.0-src+6a10ac8`. Executable SHA-256 values are in [snapshot.json](snapshot.json); retained runtime-library hashes are in [retained-kernel-library-hashes.json](retained-kernel-library-hashes.json). The recorded `leanchecker.exe` SHA-256 is `b7c503a7a984f32f04c1badb79e53e350ddb72aed530da12699e4b06357ce149`.

The 233-file project baseline includes 230 Lean files and three configuration files. Its [manifest](source-manifest-before.sha256) SHA-256 is `875e2219bcfe9ea3c6a66a21fecbb077fc225b47e4ab39a0720f82735fe8fa3a`. The original integration `.olean` SHA-256 is `b0874218a920926d711a7949ba0ba48f1d3a0014da86c399e3dfb1eedbb15ee7`. Independent copies initially matched all project bytes and all 10,056 tracked dependency files. Actual dependency HEADs matched these manifest revisions; all nine recorded dependency working trees were clean:

| Package | Revision |
|---|---|
| Mathlib | `4cbb42e75a050e830b7cf0f2ae748d7644f59cf7` |
| plausible | `d9598f07b1bc701f1e3aae163d2681c1fd978793` |
| LeanSearchClient | `ba67e212be1197b84c1f1f6299488a10a3002713` |
| importGraph | `1681d78dd6e65e38b143f9740d829c826673807c` |
| proofwidgets | `a8acbfd87375ff4abe14ce09db5b7664d383bc7f` |
| aesop | `18889deb9e83ea7420ef51c160d6f88552e744e3` |
| Qq | `507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3` |
| batteries | `4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb` |
| Cli | `ab3a82db9fea14cf0fd7f5a2de650f4b534640af` |

Repository URLs and tracked-source hashes are in [dependency-revisions.json](dependency-revisions.json) and [dependency-source-manifest-before.sha256](dependency-source-manifest-before.sha256). Vendored BanLat comprises 21 modules based on commit `5c9360ccd9cef27b749f3cabda6348fd2529d1a3`; its existing import compatibility changes and licence remain documented in [BanLat-PORTING.md](BanLat-PORTING.md) and [BanLat-LICENSE](BanLat-LICENSE).

Exact command arguments, after expanding the path abbreviations:

```text
cwd P: T/bin/lake.exe env T/bin/leanchecker.exe --fresh --verbose ComplementedSubspace
cwd R: T/bin/lake.exe --no-cache build +ComplementedSubspace:olean
cwd R: T/bin/lake.exe --no-cache env T/bin/leanchecker.exe --fresh --verbose ComplementedSubspace
```

The executed endpoint/formulation invocations use cwd `R` and the prefix `T/bin/lake.exe --no-cache env T/bin/lean.exe -j1 -M8192`, followed separately by `E/EndpointChecks.lean`, `E/PrintDefinitions.lean`, and `R/MainTheoremReview.lean`. All three returned native exit code 0 (24.094 s, 17.453 s and 19.938 s respectively). [REPRODUCE.md](REPRODUCE.md) gives portable preparation, manifest verification, commands and deadlines; the preserved runners contain the actual Windows paths and original dated deadline.

## Isolation and measured source coverage

The independently copied reproduction initially contained no compiled Lean/native artifacts, package build directories, shared Git objects, hard links, symlinks or junctions. Original build caches were retained untouched. Inherited Lean search paths were cleared; Lake-generated paths were recorded before and after the build. [Clean state](clean-state.json), [cache controls](cache-controls.json), [pre-build paths](rebuilt-search-path-before.log), [post-build paths](rebuilt-search-path-after.log).

Build/replay children used `LAKE_ARTIFACT_CACHE=false`, `LAKE_RESTORE_ARTIFACTS=false`, a private initially empty `A/isolated-lake-cache`, `MATHLIB_NO_CACHE_ON_UPDATE=1`, and `LEAN_NUM_THREADS=4`. The `--no-cache` argument disabled automatic package build-cache fetching; local artifact-cache reads were separately disabled. Mathlib's explicit restoration setting overrides the environment default, so isolation rests on these combined controls and initially absent outputs. No Mathlib cache-download command was used. These settings do not establish a universal process-count or total-memory cap. [Pinned control analysis](rebuild-controls.md).

The build produced **2,774 primary `.olean` files**: project 177 (including 21 BanLat modules and the integration root), Mathlib 2,340, aesop 132, batteries 74, Qq 14, plausible 13, proofwidgets 10, importGraph 10, LeanSearchClient 4. Cli produced none because it was unused by this target. These are actual output-inventory counts, distinct from Lake's 2,789 aggregate jobs and from any replayed-declaration count. [Coverage](coverage.json), [hashed artifact inventory](rebuilt-artifact-inventory.json).

The separate resolved-build-input check passed with native exit 0 in 114.172 s: 2,774 setup files, 9,354,642 explicit imported-artifact references, and 15,954 unique paths, all inside the reproduction, with no findings. [Small summary](resolved-build-inputs/summary.json), [native record](resolved-build-input-check.command.json). Setup files can omit core imports; Lake's environment evidence and official fresh replay account for the retained toolchain separately. The full raw module map is approximately 862 MB before compression and is reserved for the evidence archive; the local website need only serve this small summary.

The source build covered the integration root's non-toolchain imported closure. The pinned Lean/core/standard-library distribution was retained, as were canonical tracked ProofWidgets JavaScript and source-tree trace inputs. Neither Lean's compiler nor that JavaScript's TypeScript sources were rebuilt. Unrelated Mathlib modules and unused project drafts are outside this build claim.

## Five endpoints and proof interpretation

The integration root imports all five endpoint declarations. Names and types below use namespace `ComplementedSubspace`:

| Endpoint | Declared type |
|---|---|
| `realMainTheorem` | `RealMainTheoremStatement` |
| `realCorollary` | `RealCorollaryStatement` |
| `realUnconditionalCorollary` | `UnconditionalCorollaryStatement ℝ` |
| `realSeparableNonprimarity` | `SeparableNonprimarityStatement` |
| `complexCorollary` | `ComplexCorollaryStatement` |

[EndpointChecks.lean](EndpointChecks.lean) checks each proof by explicit type ascription, inspects theorem kind and closed declaration headers, prints stored types and transitive axioms, and enforces the allowlist `{propext, Classical.choice, Quot.sound}`. It also checks imported names in the project namespace. Its type ascriptions establish elaborated proof-at-type checks; they are not a separate syntactic comparison of stored expressions. The completed run found all five declarations to be theorems with no universe or outer theorem parameters. The actual stored types agree with the table. Each of the five printed exactly `[propext, Classical.choice, Quot.sound]`; no additional axiom was found. The separate namespace traversal checked 2,573 imported `ComplementedSubspace` declarations against the same allowlist and passed.

[PrintDefinitions.lean](PrintDefinitions.lean) prints all five statement definitions and twenty project definitions. The unchanged `MainTheoremReview.lean` checks the existing real-main formulation identities by `rfl`. All 25 requested definition bodies were printed successfully, the formulation review returned exit 0, and 82 website source snippets/context captures matched the reproduced source under CRLF-to-LF normalization only. The full source files, literal bodies and implicit contexts retain the existing paper mapping. Formal acceptance and displayed-definition identity do not independently prove correspondence with the manuscript's intended mathematics.

## Replay trust boundary and preserved evidence

The official pinned [checker source](pinned-LeanChecker.lean) and [replay source](pinned-Replay.lean) implement `--fresh` by replaying imported constants into an empty kernel environment. Safe logical declarations from imported core libraries participate; unsafe/partial declarations are skipped by the official algorithm. Axioms remain assumptions. Structural loading of compiled files and the retained toolchain remain within the declared computational trust boundary. Verbose output supplies no declaration-count certificate. [Provenance and scope](checker-provenance-and-scope.md).

This is locally assembled reproducible checking with the official Lean kernel, without independent third-party certification or a separately implemented kernel. Hashes identify bytes; they are not an external authority's signature.

The original Git repository has an unborn HEAD. Its `git rev-parse HEAD` returned the expected **128**, preserved as a failed metadata command in [project-git-head.log](project-git-head.log); source identity therefore uses manifests, not an invented commit. Existing build warnings remain unedited in raw output. Prior audit/checkpoint evidence, including historical helper failures, remains preserved. Native stdout/stderr and real exit codes are retained separately; a concatenated display log does not imply chronological stream interleaving.

Evidence is local-only and raw records retain workstation paths. [Source archive validation](source-archive-validation.json) records the exact frozen-project and dependency-source archives; rebuilding solely from their extracted distributable contents was not performed. Final original/reproduced project and dependency hashes matched all baseline bytes. The previous audit files, original root artifact, frozen source archive, checker binaries, runtime libraries and reference checker sources remained unchanged. The source archive and final evidence archive were checked by CRC, exact member set and SHA-256; the final archive digest is detached to avoid self-reference.


## Supplementary source findings

The lexical scan covered 2,831 Lean files: 177 imported local modules, 53 other local files, two new audit helpers, two reference copies of the official checker/replay source, and 2,597 built external module sources. There were zero imported-project placeholder/trust-override gate hits. The project's transparency, heartbeat and three scoped `allowUnsafeReducibility` settings are recorded; their spelling alone does not constitute a kernel bypass.

The external code-class findings include six `sorry`, four `admit` and five `sorryAx` spellings. Some are actual placeholder-generating metaprograms in LeanSearchClient, Aesop script scaffolding and `calc?`; others are option identifiers, recognizers or hover metadata. These findings have been retained and individually reviewed, not suppressed. No external code-class `axiom`, `native_decide`, `ofReduceBool`, `trust`, `trustLevel` or `skipKernelTC` occurrence was recorded in this selected source scope. General unsafe/partial/metaprogram implementations were not all separately verified for correctness.

[Reviewed contexts and counts](source-scan-review.md), [complete lexical occurrences](identity-lexical-occurrences.jsonl), [scanned-source inventory](identity-lexical-source-inventory.json). This textual review is supplementary. The actual transitive checks rule out extra axiom dependencies for the claimed endpoint proofs and the audited project namespace; the official fresh replay checks the resulting safe logical declarations.

## Final preservation, archive and scope

After all Lean invocations finished, a further hash pass checked each original and reproduced project tree (233 files each) and each original and reproduced dependency tree (10,056 tracked files each). Every hash matched. The original and newly rebuilt integration root have the same SHA-256, `b0874218a920926d711a7949ba0ba48f1d3a0014da86c399e3dfb1eedbb15ee7`; this is an observed artifact identity, not a substitute for the independent source build.

[Final native check](final-preservation-check.log), [preservation details](final-preservation.json), [unchanged project manifest](source-manifest-after.sha256). No mathematical source, proof, definition, notation, instance, dependency revision or foundational allowlist was repaired or changed in this audit. All Lean, checker and source/axiom identity checks passed on their recorded runs. The report-assembly script initially failed to read UTF-8 text using Windows' default encoding. That presentation-tool failure was preserved, reproduced with native logging, repaired by explicitly selecting UTF-8, and retried; see [repair record](report-assembly-repair.md), [captured failure](report-assembly-encoding-failure.log), and [successful retry](report-assembly-retry.log). The expected unborn-HEAD metadata probe is distinguished above. Raw diagnostics and exit codes are unedited.

The downloadable [evidence archive](../full-fresh-audit-evidence.zip) contains the run records and separate raw streams, all audit helper sources, manifests, full module/path map, source archives, exact statement/definition output and reproduction notes. `CONTENTS.sha256` covers every member except itself. The [detached receipt](../archive-validation.json) records the final archive SHA-256, all-member CRC/SHA validation, file count and full elapsed audit time. The final packaging command and its receipt remain outside the archive to avoid a self-referential hash. Checkpoint archives of the earlier website and audit remain separately preserved locally.

This records source reproduction, kernel replay and axiom checks for the listed formal statements. It uses Lean's own kernel and the stated foundational assumptions; it is not verification by a separate kernel implementation. The correspondence between the formal statements and the paper is reviewed and explained separately. Alternative formal proofs do not certify every step of a different manuscript proof.

Everything remains local and unpublished: no uploads, repository pushes, cache publication or external preview were performed. Raw evidence includes the Windows username and personal paths. It is an unredacted local original; review a separately labelled, separately manifested redacted copy before any eventual public release. The compact companion link belongs on the existing Verification page and records this snapshot, not future source edits or live CI.
