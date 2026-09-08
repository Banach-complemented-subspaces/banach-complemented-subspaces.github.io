> Companion-site derivative: the report text below is preserved, while file hyperlinks are made portable. Raw files link directly when included in the local companion assets; remaining links explicitly name an entry in the full audit ZIP. Source line numbers remain in link labels. The unchanged [original report](raw/audit/verification_report.md) has SHA256 `5ee6b720af87fb151af8c7bda3ca525eb1fe3de6226f2f19edd41e9e5b02ec4f`.

# Independent Lean verification report

**LEAN VERIFICATION CERTIFICATE: PASS**

**Result: PASS**

Generated UTC: 2026-09-05T23:29:14.226751+00:00.

Target: `ComplementedSubspace.realMainTheorem : ComplementedSubspace.RealMainTheoremStatement`, in [ComplementedSubspace/RealMainTheorem.lean:15](raw/source/ComplementedSubspace/RealMainTheorem.lean).

Scope: mechanical verification of the actual stored Lean declaration, its compiled dependencies, the local source scan, and delivery provenance. This report makes no manuscript or natural-language faithfulness assessment.

**Final result: PASS**

All required compiler steps, source/provenance checks, and complete kernel-graph checks succeeded in the evidence read by this generator. The certificate is relative to the recorded Lean runtime, external dependency artifacts, and the three logical axioms listed below.

The compiler pipeline currently records `passed` at `all compiler checks and source immutability passed`. Guard details: [report_guard_results.json](raw/audit/report_guard_results.json).

## Audit-helper failures and corrections

### Unsupported display option

The initial audit attempt failed in the identity display helper after the fresh root build and direct theorem-source check had succeeded. The preserved failed command exited **1** with this diagnostic:

```text
verification/independent-audit-2026-09-05/MainIdentity.lean:5:0: error: Unknown option `pp.width`
```

The exact original failure remains in [initial_failed_theorem_check.txt](raw/audit/initial_failed_theorem_check.txt) and [initial_failed_run_status.json](raw/audit/initial_failed_run_status.json). Both `#check` lines, the theorem print, the three-axiom output, and the stored-type assertion were printed during that failed attempt; they do not satisfy the required successful identity check because the process exited 1.

The correction removes the unsupported pretty-printing command `set_option pp.width 110` from line 5 of each of the two audit-only helpers, `MainIdentity.lean` and `PrintDefinitions.lean`. The generator compares the preserved and current helper bytes and requires that single removed line to be their entire difference; it also requires the preserved originals to match the initial scanner hashes. The original mathematical source and pinned configuration are checked separately against the unchanged initial SHA256 snapshot.

| Audit helper | Preserved original | Exact single display-option removal |
|---|---|---|
| [MainIdentity.lean](raw/audit/MainIdentity.lean) | [MainIdentity.before_formatter_fix.txt](raw/audit/MainIdentity.before_formatter_fix.txt) | `True` |
| [PrintDefinitions.lean](raw/audit/PrintDefinitions.lean) | [PrintDefinitions.before_formatter_fix.txt](raw/audit/PrintDefinitions.before_formatter_fix.txt) | `True` |

The retained fresh build finished at 2026-09-05T23:08:14.5354564Z with exit 0; the direct mathematical-source check finished at 2026-09-05T23:08:44.5780120Z with exit 0. Their successful commands/results and original raw logs are retained. Timestamp instants are unchanged; PowerShell's JSON round-trip may shorten trailing fractional zeroes in the retained record timestamps.

The correction-resume runner is [resume_after_formatter_fix.ps1](raw/audit/resume_after_formatter_fix.ps1). The final run status must record `resumedFrom: initial_failed_run_status.json`, preserve the successful first three commands, and contain successful reruns of all remaining five checks. Current resume marker: `initial_failed_run_status.json`. This history remains in the report even when the final certificate passes.

### IO lifting in the dependency audit helper

A second audit attempt reached seven successful core steps, then failed while elaborating `TraceDependencies.lean`. Ten unqualified `liftIO` calls resolved to `CommandElabM` inside an inspector declared in `MetaM`. The preserved failed helper exited **1** with the following ten type errors and one resulting evaluation refusal:

```text
verification/independent-audit-2026-09-05/TraceDependencies.lean:59:2: error: Type mismatch
verification/independent-audit-2026-09-05/TraceDependencies.lean:60:17: error: Type mismatch
verification/independent-audit-2026-09-05/TraceDependencies.lean:61:17: error: Type mismatch
verification/independent-audit-2026-09-05/TraceDependencies.lean:62:19: error: Type mismatch
verification/independent-audit-2026-09-05/TraceDependencies.lean:83:6: error: Type mismatch
verification/independent-audit-2026-09-05/TraceDependencies.lean:117:6: error: Type mismatch
verification/independent-audit-2026-09-05/TraceDependencies.lean:136:10: error: Type mismatch
verification/independent-audit-2026-09-05/TraceDependencies.lean:140:12: error: Type mismatch
verification/independent-audit-2026-09-05/TraceDependencies.lean:176:2: error: Type mismatch
verification/independent-audit-2026-09-05/TraceDependencies.lean:177:2: error: Type mismatch
verification/independent-audit-2026-09-05/TraceDependencies.lean:191:0: error: Aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
```

Complete diagnostics and state: [initial_failed_dependency_trace.txt](raw/audit/initial_failed_dependency_trace.txt), [second_failed_run_status.json](raw/audit/second_failed_run_status.json). Original helper: [TraceDependencies.before_io_fix.txt](raw/audit/TraceDependencies.before_io_fix.txt); its prior scanner hash is preserved in [before_io_placeholder_scan.json](raw/audit/before_io_placeholder_scan.json).

The `sorry` message concerns compiler recovery placeholders created when the audit helper failed to elaborate; Lean then refused to evaluate that failed helper. The main theorem had already compiled, and its separate successful axiom checks reported only `propext`, `Classical.choice`, and `Quot.sound`. The failed helper run supplies no passing dependency-graph evidence. The complete graph and final successful traversal remain mandatory gates.

The correction changes exactly these ten IO-lift calls, leaving the traversal logic and `run_cmd` entry unchanged:

```lean
-- Preserved audit helper
liftIO <| ...
-- Corrected audit helper
liftM (m := IO) (n := MetaM) <| ...
```

Exact byte-replacement check: `True`; replacement count: `10`. No `#eval!`, kernel-check disable option, or trust override is permitted by the correction guard. Original mathematical files remain subject to the unchanged-source checks below.

The retry uses [resume_after_formatter_fix.ps1](raw/audit/resume_after_formatter_fix.ps1) with `-ResumeDependencyWalker`, retaining the first seven successful command results and rerunning the walker. A successful final state must include `dependencyResumedFrom: second_failed_run_status.json`; current marker: `second_failed_run_status.json`. Both audit-helper failures and their narrow corrections remain documented even if the final certificate passes.

## Environment and source provenance

Recorded native Windows command line (invoked directly by the collector):

```text
"WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lean.exe" --version
```

```text
Lean (version 4.34.0-rc2, x86_64-w64-windows-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)
```

Exit code: `0`; working directory: `LEAN_PROJECT`.

Recorded native Windows command line (invoked directly by the collector):

```text
"WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe" --version
```

```text
Lake version 5.0.0-src+6a10ac8 (Lean version 4.34.0-rc2)
```

Exit code: `0`; working directory: `LEAN_PROJECT`.

Exact configuration contents, binary hashes, stdout/stderr, commands, and exit codes: [environment.txt](raw/audit/environment.txt). The toolchain file records `leanprover/lean4:v4.34.0-rc2`.

The enclosing IA-Stuff-Math Git repository has an unborn `refs/heads/master`: `git rev-parse --verify HEAD` returns exit 128, and its status contains untracked files. There is no project commit hash to report. The audit identifies the project source by SHA256 snapshots and the delivery archive. Full commands and actual Git output are preserved in [git_status.txt](raw/audit/git_status.txt).

| Dependency | Manifest revision | Recorded actual HEAD | Clean status |
|---|---|---|---|
| `plausible` | `d9598f07b1bc701f1e3aae163d2681c1fd978793` | `d9598f07b1bc701f1e3aae163d2681c1fd978793` | `True` |
| `LeanSearchClient` | `ba67e212be1197b84c1f1f6299488a10a3002713` | `ba67e212be1197b84c1f1f6299488a10a3002713` | `True` |
| `importGraph` | `1681d78dd6e65e38b143f9740d829c826673807c` | `1681d78dd6e65e38b143f9740d829c826673807c` | `True` |
| `proofwidgets` | `a8acbfd87375ff4abe14ce09db5b7664d383bc7f` | `a8acbfd87375ff4abe14ce09db5b7664d383bc7f` | `True` |
| `aesop` | `18889deb9e83ea7420ef51c160d6f88552e744e3` | `18889deb9e83ea7420ef51c160d6f88552e744e3` | `True` |
| `Qq` | `507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3` | `507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3` | `True` |
| `batteries` | `4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb` | `4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb` | `True` |
| `Cli` | `ab3a82db9fea14cf0fd7f5a2de650f4b534640af` | `ab3a82db9fea14cf0fd7f5a2de650f4b534640af` | `True` |
| `mathlib` | `4cbb42e75a050e830b7cf0f2ae748d7644f59cf7` | `4cbb42e75a050e830b7cf0f2ae748d7644f59cf7` | `True` |

Every dependency checkout's own repository identity, HEAD, origin URL, status, tracked source diff, and untracked Lean-source list is recorded in [dependency_provenance.txt](raw/audit/dependency_provenance.txt). The fresh project build retains external `.lake/packages` caches; this audit does not claim to rebuild the whole Lean standard library or Mathlib from source.

Delivery: [Complemented_Subspace_Lean_Verified.PUBLIC.zip](downloads/Complemented_Subspace_Lean_Verified.PUBLIC.zip). Recorded size: `598251` bytes; SHA256:

```text
5fc920bc7bb22592c2170ac72447af563d17ef261e7f39dfd6123ba04b074148
```

Archive comparison records 183/183 matching Lean/configuration files, and 261/261 verified internal source-manifest entries. ZIP CRC and duplicate-entry results are in [archive_comparison.json](raw/audit/archive_comparison.json). `SOURCE-MANIFEST.sha256` is generated inside the archive and has no workspace original; local extra audit/scratch/draft files are separately listed in that evidence.

## Fresh build and exact theorem checks

```text
Validated absolute clean target: LEAN_PROJECT\.lake\build
External .lake/packages dependency caches are retained; all root-project and vendored BanLat build artifacts are removed.
LEAN_NUM_THREADS=2; each project compiler uses -j1 -M8192 from lakefile.toml.
Root build .olean files after clean: 0
```

Configured-root local import closure: **177 modules**, derived from the scanner's recorded import inventory. Original Lean source files in the before/after snapshot: **230**. Total scanner inventory, including this audit's Lean helpers: **234** files. The source scan includes unused drafts; those drafts are not asserted to have been compiled. The theorem module's own local syntactic import closure has 148 modules; the kernel proof-dependency graph below is a separate, declaration-level traversal.

The raw build log currently contains `Built` records for 177/177 local root-closure modules. PASS requires all 177 records and the resulting `.olean` files. The build uses the configured root `ComplementedSubspace` and its full local dependency closure, including vendored BanLat. Root build products are removed first; post-clean `.olean` count is taken from the actual evidence above. External dependency caches are retained. Compiler commands and outcomes:

**clean** — [clean.log](raw/audit/clean.log)

```powershell
& 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' '--no-cache' 'clean' 'complemented_subspace_trial'
```

Exit code: `0`; UTC 2026-09-05T22:40:09.1896145Z to 2026-09-05T22:40:11.6873016Z.

**build** — [build.log](raw/audit/build.log)

```powershell
& 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' '--no-cache' 'build' '+ComplementedSubspace:olean'
```

Exit code: `0`; UTC 2026-09-05T22:40:11.7222835Z to 2026-09-05T23:08:14.5354564Z.

**direct main source check** — [main_source_check.log](raw/audit/main_source_check.log)

```powershell
& 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' '--no-cache' 'env' 'lean' '-j1' '-M8192' 'ComplementedSubspace/RealMainTheorem.lean'
```

Exit code: `0`; UTC 2026-09-05T23:08:14.5578763Z to 2026-09-05T23:08:44.578012Z.

**theorem identity** — [theorem_check.txt](raw/audit/theorem_check.txt)

```powershell
& 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' '--no-cache' 'env' 'lean' '-j1' '-M8192' 'verification/independent-audit-2026-09-05/MainIdentity.lean'
```

Exit code: `0`; UTC 2026-09-05T23:13:51.2241901Z to 2026-09-05T23:14:50.8299027Z.

**exact definitions** — [definitions.txt](raw/audit/definitions.txt)

```powershell
& 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' '--no-cache' 'env' 'lean' '-j1' '-M8192' 'verification/independent-audit-2026-09-05/PrintDefinitions.lean'
```

Exit code: `0`; UTC 2026-09-05T23:14:50.8686342Z to 2026-09-05T23:15:29.7061797Z.

**axioms** — [axioms.txt](raw/audit/axioms.txt)

```powershell
& 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' '--no-cache' 'env' 'lean' '-j1' '-M8192' 'verification/independent-audit-2026-09-05/PrintAxioms.lean'
```

Exit code: `0`; UTC 2026-09-05T23:15:29.7442669Z to 2026-09-05T23:15:55.8644073Z.

**whole imported project axiom audit** — [whole_project_axioms.txt](raw/audit/whole_project_axioms.txt)

```powershell
& 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' '--no-cache' 'env' 'lean' '-j1' '-M8192' 'WholeProjectAudit.lean'
```

Exit code: `0`; UTC 2026-09-05T23:15:55.9165438Z to 2026-09-05T23:16:19.9147602Z.

**kernel dependency traversal** — [dependency_trace_run.txt](raw/audit/dependency_trace_run.txt)

```powershell
& 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' '--no-cache' 'env' 'lean' '-j1' '-M8192' 'verification/independent-audit-2026-09-05/TraceDependencies.lean'
```

Exit code: `0`; UTC 2026-09-05T23:21:32.3816422Z to 2026-09-05T23:22:16.8966330Z.

**Supplemental build of all remaining library modules** — [additional_modules_build.log](raw/audit/additional_modules_build.log)

The present library tree comprises 193 modules: root 1, ComplementedSubspace 171, and BanLat 21. The configured-root build scope has 177 modules; the supplemental command explicitly targets the remaining 16 modules, including library audit files and the otherwise unused library lemmas. Exact module/target coverage is recorded in [build_scope.json](raw/audit/build_scope.json). Root-level scratch files and experimental drafts remain in the source scan and are not claimed as compiled library modules.

```powershell
& 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' '--no-cache' 'build' '+ComplementedSubspace.ComplexCorollaryAudit:olean' '+ComplementedSubspace.ComplexRealDPRAudit:olean' '+ComplementedSubspace.FiniteHilbertWitnessAudit:olean' '+ComplementedSubspace.FiniteOverlapScaleAudit:olean' '+ComplementedSubspace.FiniteParameterAudit:olean' '+ComplementedSubspace.LocalHilbertAudit:olean' '+ComplementedSubspace.LocalHilbertDualTopAudit:olean' '+ComplementedSubspace.LocalHilbertQuotientAudit:olean' '+ComplementedSubspace.LocalHilbertRecursiveQuotient:olean' '+ComplementedSubspace.ProductFrameTranspose:olean' '+ComplementedSubspace.ProjectionAssemblyAudit:olean' '+ComplementedSubspace.PureFrameDPRAudit:olean' '+ComplementedSubspace.RealMainAudit:olean' '+ComplementedSubspace.RealMainConsequencesAudit:olean' '+ComplementedSubspace.RecursiveParametersAudit:olean' '+ComplementedSubspace.SelectedFrameBasis:olean'
```

Supplemental status: `passed`; exit code: `0`; source unchanged: `True`; UTC 2026-09-05T23:23:37.2559236Z to 2026-09-05T23:27:47.3964378Z.

Supplemental status/source evidence: [additional_build_status.json](raw/audit/additional_build_status.json), [additional_source_unchanged.txt](raw/audit/additional_source_unchanged.txt). Verified supplemental `Built` coverage is 16/16 modules. PASS requires successful compilation of the entire 193-module present library tree and unchanged original sources.

The independent identity helper executes both `#check` forms, assigns the existing theorem to the requested proposition in an `example`, and inspects `env.checked.get` for `.thmInfo`. Its stored-type check uses exact expression equality with the statement constant and requires no universe parameters. The exact assertion text is:

```text
KERNEL DECLARATION CHECK: theorem; exact stored type ComplementedSubspace.RealMainTheoremStatement; no parameters.
```

The guard requires this text in a successful compiler log; it is not inferred from the helper's source alone. Actual `#check`, theorem print, and assertion output: [theorem_check.txt](raw/audit/theorem_check.txt); audit helper: [MainIdentity.lean](raw/audit/MainIdentity.lean).

Actual identity-check terminal output:

```text
ComplementedSubspace.realMainTheorem : ComplementedSubspace.RealMainTheoremStatement
ComplementedSubspace.realMainTheorem : ComplementedSubspace.RealMainTheoremStatement
theorem ComplementedSubspace.realMainTheorem : ComplementedSubspace.RealMainTheoremStatement :=
fun ρ hρ =>
  Exists.casesOn
    (ComplementedSubspace.exists_recursive_alternatingProjection_near_one
      (lt_of_not_ge fun a =>
        Mathlib.Tactic.Linarith.lt_irrefl
          (Eq.mp
            (congrArg (fun _a => _a < 0)
              (Mathlib.Tactic.Ring.of_eq
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf ρ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ρ ^ Nat.rawCast 1 * Nat.rawCast 1 = ρ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (ρ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul ρ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add (ρ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                      (Mathlib.Tactic.Ring.Common.atom_pf ρ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ρ ^ Nat.rawCast 1 * Nat.rawCast 1 = ρ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (ρ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add (ρ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                    (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero (ρ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ρ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
            (Mathlib.Tactic.Linarith.add_lt_of_neg_of_le (Mathlib.Tactic.Linarith.sub_neg_of_lt hρ)
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le a)))))
    fun η h =>
    Exists.casesOn h fun hη h =>
      Exists.casesOn h fun P h =>
        And.casesOn h fun hPP right =>
          And.casesOn right fun hP1 right =>
            And.casesOn right fun hP right =>
              And.casesOn right fun hPc1 right =>
                And.casesOn right fun hPc hcoords =>
                  let s := ComplementedSubspace.recursiveFrameSelection hη;
                  Exists.intro s.toBlockParameters
                    ⟨inferInstance,
                      ⟨inferInstance,
                        ⟨ComplementedSubspace.ambient_hasRealBanachLatticeOrder s.toBlockParameters,
                          Exists.intro P
                            ⟨hPP,
                              ⟨hP,
                                ⟨hPc,
                                  ⟨ComplementedSubspace.hasSeparatedRange_of_DPR_obstructions P hPP
                                      (ComplementedSubspace.ambient_chiGL_le_one s.toBlockParameters)
                                      (ComplementedSubspace.ambientDual_chiGL_le_one s.toBlockParameters)
                                      (ComplementedSubspace.actualProjection_range_chiDPR_eq_top s P hcoords)
                                      (ComplementedSubspace.actualProjection_range_dual_chiDPR_eq_top s P hcoords),
                                    ComplementedSubspace.hasSeparatedRange_of_DPR_obstructions
                                      (ContinuousLinearMap.id ℝ ↥(ComplementedSubspace.Ambient s.toBlockParameters) - P)
                                      (ComplementedSubspace.complement_idempotent P hPP)
                                      (ComplementedSubspace.ambient_chiGL_le_one s.toBlockParameters)
                                      (ComplementedSubspace.ambientDual_chiGL_le_one s.toBlockParameters)
                                      (ComplementedSubspace.actualProjection_complement_range_chiDPR_eq_top s P hcoords)
                                      (ComplementedSubspace.actualProjection_complement_range_dual_chiDPR_eq_top s P
                                        hcoords)⟩⟩⟩⟩⟩⟩⟩
'ComplementedSubspace.realMainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
KERNEL DECLARATION CHECK: theorem; exact stored type ComplementedSubspace.RealMainTheoremStatement; no parameters.
```

Source immutability result:

```text
PASS: all 233 original local Lean/configuration files are unchanged by SHA256.
```

The generator also compares the original current files to [source_hashes_after.json](raw/audit/source_hashes_after.json) and compares all original scanned Lean hashes to [source_hashes_before.json](raw/audit/source_hashes_before.json). It checked 233 current original source/configuration files at report generation.

## Placeholder scan and local reducibility settings

Method: Conservative source-text token scan after nested-comment, character/string/raw-string-aware lexing; ! string interpolation code is retained. Not an elaborator/kernel replacement.

| Executable token | Count |
|---|---|
| `sorry` | 0 |
| `admit` | 0 |
| `sorryAx` | 0 |
| `axiom` | 0 |
| `unsafe` | 0 |
| `partial` | 0 |
| `opaque` | 0 |
| `native_decide` | 0 |
| `implemented_by` | 0 |
| `extern` | 0 |
| `allowUnsafeReducibility` | 3 |

Lexical/import errors: `[]`. Placeholder/trust-bypass candidates: `[]`. Raw inventory, source/comment distinctions, all settings, metaprogramming contexts, and exact scanner/search commands with exit codes: [placeholder_audit.txt](raw/audit/placeholder_audit.txt), [placeholder_scan.json](raw/audit/placeholder_scan.json), [local-source-inventory.txt (in full audit ZIP: `audit-evidence/local-source-inventory.txt`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip).

The source scanner records three local `allowUnsafeReducibility` occurrences and their immediately following attribute commands:

[ComplementedSubspace/ProductFrameMoments.lean:10](raw/source/ComplementedSubspace/ProductFrameMoments.lean)

```lean
10: set_option allowUnsafeReducibility true in
11: attribute [local reducible] Matrix MomentIndex FrameIndex
```

[ComplementedSubspace/ProductFrameSymmetry.lean:6](raw/source/ComplementedSubspace/ProductFrameSymmetry.lean)

```lean
6: set_option allowUnsafeReducibility true in
7: attribute [local reducible] MomentIndex FrameIndex
```

[ComplementedSubspace/ProductFrameTrace.lean:69](raw/source/ComplementedSubspace/ProductFrameTrace.lean)

```lean
69: set_option allowUnsafeReducibility true in
70: attribute [local reducible] FrameCoefficient Matrix
```

The captured implementation in [pinned Lean ReducibilityAttrs.lean:122](raw/runtime/Lean/ReducibilityAttrs.lean) makes this option bypass reducibility-attribute validation before updating an elaborator reducibility extension. It affects elaboration, simplifier/typeclass indexing, and local unfolding control; it does not disable kernel proof checking or itself introduce an axiom. The exact pinned implementation excerpt and hash are in `allowUnsafeReducibility_implementation_evidence` in [placeholder_scan.json](raw/audit/placeholder_scan.json). The kernel traversal separately inspects every reachable project declaration for axiom, opaque, unsafe, and partial flags.

The scanner's `constants` token occurrence is the environment-field access `env.constants.toList` in `WholeProjectAudit.lean`; it is not a mathematical constant declaration. Source-inspection audit `run_cmd` blocks are recorded separately and do not supply the target with a proof premise. The token scan is supporting source evidence, with the compiler and checked-environment traversal providing separate checks.

## Exact axioms and compiled dependency graph

Actual terminal output of `#print axioms ComplementedSubspace.realMainTheorem`:

```text
'ComplementedSubspace.realMainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α
axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
```

`propext` is propositional extensionality: logically equivalent propositions can be equal. `Classical.choice` supplies classical choice from a nonempty type. `Quot.sound` identifies quotient classes when their representatives satisfy the quotient relation. These are the standard Lean axioms against which the certificate is checked; no additional reachable axiom is accepted by this report's guard.

| Kernel graph measurement | Recorded value |
|---|---|
| `traversal_complete` | `True` |
| `ownership_classification_complete` | `True` |
| `axiom_cross_check_agrees` | `True` |
| `queued_nodes` | `40291` |
| `processed_nodes` | `40291` |
| `checked_constants` | `40291` |
| `project_constants` | `1946` |
| `edges` | `1332580` |
| Project defining modules actually reached | `136` |
| Project axiom/opaque/unsafe/partial declarations | `[]` |

The traversal starts at the actual checked theorem and follows declaration types and available values, including theorem proofs and opaque bodies via `allowOpaque := true`, plus inductive-constructor edges. It cross-checks its axiom set against stock `collectAxioms`. Project ownership uses the defining imported module, so private generated names are included. Missing constants, missing bodies, missing origins, incomplete traversal, and unexpected project declaration kinds prevent PASS.

The generator also reads the raw graph to check node/edge counts, endpoint coverage, project origins, axiom flags, and immediate-reference records. Graph evidence: [kernel_dependency_summary.json](raw/audit/kernel_dependency_summary.json), [dependency_nodes.jsonl (in full audit ZIP: `audit-evidence/dependency_nodes.jsonl`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip), [dependency_edges.jsonl (in full audit ZIP: `audit-evidence/dependency_edges.jsonl`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip), [dependency_direct.jsonl](raw/audit/dependency_direct.jsonl), [dependency_trace.txt](raw/audit/dependency_trace.txt).

Immediate project-owned references in the actual kernel graph:

| Declaration | Defining module |
|---|---|
| `ComplementedSubspace.Ambient` | `ComplementedSubspace.Ambient` |
| `ComplementedSubspace.Ambient._proof_1` | `ComplementedSubspace.Ambient` |
| `ComplementedSubspace.Block` | `ComplementedSubspace.Ambient` |
| `ComplementedSubspace.BlockParameters` | `ComplementedSubspace.Ambient` |
| `ComplementedSubspace.BlockParameters.dimension` | `ComplementedSubspace.Ambient` |
| `ComplementedSubspace.BlockParameters.exponent` | `ComplementedSubspace.Ambient` |
| `ComplementedSubspace.HasRealBanachLatticeOrder` | `ComplementedSubspace.TheoremStatement` |
| `ComplementedSubspace.HasSeparatedRange` | `ComplementedSubspace.TheoremStatement` |
| `ComplementedSubspace.RealMainTheoremStatement` | `ComplementedSubspace.TheoremStatement` |
| `ComplementedSubspace.RealMainTheoremStatement._proof_1` | `ComplementedSubspace.TheoremStatement` |
| `ComplementedSubspace.RealMainTheoremStatement._proof_2` | `ComplementedSubspace.TheoremStatement` |
| `ComplementedSubspace.RealMainTheoremStatement._proof_3` | `ComplementedSubspace.TheoremStatement` |
| `ComplementedSubspace.RealMainTheoremStatement._proof_4` | `ComplementedSubspace.TheoremStatement` |
| `ComplementedSubspace.RealMainTheoremStatement._proof_5` | `ComplementedSubspace.TheoremStatement` |
| `ComplementedSubspace.RecursiveFrameSelection` | `ComplementedSubspace.RecursiveParameters` |
| `ComplementedSubspace.RecursiveFrameSelection.alternatingBlockProjection` | `ComplementedSubspace.RecursiveProjection` |
| `ComplementedSubspace.RecursiveFrameSelection.toBlockParameters` | `ComplementedSubspace.RecursiveParameters` |
| `ComplementedSubspace.actualProjection_complement_range_chiDPR_eq_top` | `ComplementedSubspace.ActualProjectionDPR` |
| `ComplementedSubspace.actualProjection_complement_range_dual_chiDPR_eq_top` | `ComplementedSubspace.ActualProjectionDualDPR` |
| `ComplementedSubspace.actualProjection_range_chiDPR_eq_top` | `ComplementedSubspace.ActualProjectionDPR` |
| `ComplementedSubspace.actualProjection_range_dual_chiDPR_eq_top` | `ComplementedSubspace.ActualProjectionDualDPR` |
| `ComplementedSubspace.ambientDual_chiGL_le_one` | `ComplementedSubspace.AmbientFiniteApproximation` |
| `ComplementedSubspace.ambientSeparableSpace` | `ComplementedSubspace.AmbientSeparable` |
| `ComplementedSubspace.ambientUniformConvexSpace` | `ComplementedSubspace.AmbientUniformConvex` |
| `ComplementedSubspace.ambient_chiGL_le_one` | `ComplementedSubspace.AmbientFiniteApproximation` |
| `ComplementedSubspace.ambient_hasRealBanachLatticeOrder` | `ComplementedSubspace.AmbientLattice` |
| `ComplementedSubspace.complement_idempotent` | `ComplementedSubspace.RecursiveProjection` |
| `ComplementedSubspace.exists_recursive_alternatingProjection_near_one` | `ComplementedSubspace.RecursiveProjection` |
| `ComplementedSubspace.hasSeparatedRange_of_DPR_obstructions` | `ComplementedSubspace.ProjectionCorollaries` |
| `ComplementedSubspace.instFactLeENNRealOfNatOfRealExponent` | `ComplementedSubspace.Ambient` |
| `ComplementedSubspace.recursiveFrameExponentTolerance` | `ComplementedSubspace.RecursiveParameters` |
| `ComplementedSubspace.recursiveFrameSelection` | `ComplementedSubspace.RecursiveParameters` |
| `NormedVectorLattice.instNormedSpace` | `BanLat.Normed` |
| `instNormedVectorLatticeReal` | `BanLat.Normed` |

The concise source dependency map in [dependency_summary.md](raw/audit/dependency_summary.md) traces recursive projection/parameter construction, primal and dual DPR obstructions, local Hilbert estimates, GL retraction/approximation bounds, and ambient geometry. It distinguishes definitions, proved helper claims, and intermediate hypotheses discharged by later proofs. Mechanically located source declarations and hashes: [dependency_source_map.json](raw/audit/dependency_source_map.json). This prose map supplements the complete graph; it is not substituted for the graph's completion check.

## Exact definitions and source capture

The independent print helper prints the thirteen requested definitions and structures plus the supporting `Block` abbreviation from the compiled theorem environment:

`ComplementedSubspace.RealMainTheoremStatement`, `ComplementedSubspace.HasSeparatedRange`, `ComplementedSubspace.HasRealBanachLatticeOrder`, `ComplementedSubspace.BlockParameters`, `ComplementedSubspace.Ambient`, `ComplementedSubspace.Block`, `ComplementedSubspace.chiGL`, `ComplementedSubspace.lambdaGL`, `ComplementedSubspace.GLFactorization`, `ComplementedSubspace.chiDPR`, `ComplementedSubspace.lambdaDPR`, `ComplementedSubspace.unconditionalConstant`, `ComplementedSubspace.unconditionalBasisConstant`, `ComplementedSubspace.basisMultiplier`.

Full untruncated compiler output is preserved in [definitions.txt](raw/audit/definitions.txt) and reproduced in the appendix below. The pipeline's actual filename is `definitions.txt`. Exact original source capture with line numbers is in [definition_source_files.txt](raw/audit/definition_source_files.txt); the separate print helper is [PrintDefinitions.lean](raw/audit/PrintDefinitions.lean). These are the formal objects audited, with no natural-language interpretation verdict attached.

## Raw evidence inventory

All files present in this evidence directory when the report was generated are listed below. The generated report and guard-result JSON are outputs of this inventory operation and are omitted to avoid circular hashes. Paths are absolute and clickable; hashes identify the evidence snapshot.

| File | Bytes | SHA256 |
|---|---:|---|
| [additional_build_status.json](raw/audit/additional_build_status.json) | 2322 | `c2eaa9b0f65e0ef8170ae9f1fab9872e96ac7f5db9321321a8f32eed1be3bd93` |
| [additional_modules_build.log](raw/audit/additional_modules_build.log) | 101466 | `16880dfc34a5829d16a018cbcefe01177d8429ad721c00f72ef000c0fb92ea73` |
| [additional_source_unchanged.txt](raw/audit/additional_source_unchanged.txt) | 132 | `77eac8cd092190d3763bb8d67aff271cf6120ddf792cf2b1659f06451bfe4d26` |
| [archive_comparison.json](raw/audit/archive_comparison.json) | 100363 | `827fb27c6e76fba0b9cdc02125b80106b2672d4b5491b1c75164931e0bd08338` |
| [audit_failure.txt](raw/audit/audit_failure.txt) | 136 | `613a322919f7ef98e490c9a049029ba66c07a3f12c888fca268f9fb760367147` |
| [axioms.txt](raw/audit/axioms.txt) | 811 | `1629af12eafcb44e438e926de6705c59c15751dc56dcbe1e53fb3ffce82a2fb8` |
| [before_io_placeholder_scan.json](raw/audit/before_io_placeholder_scan.json) | 291172 | `aa007dd4af1c7eec847d9f61a6e24966e870e8ebb2c0079125e61da1b48e9cfa` |
| [build.log](raw/audit/build.log) | 87539 | `95f947e4db3f8a169548b70ca7e1a161e6a135314e29bb6117f903874d7a9c88` |
| [build_scope.json](raw/audit/build_scope.json) | 15743 | `abda9b50c6dd8fd8639de761995ec22dc853cdeb236353580a8d635bc563ae18` |
| [build_scope.md](raw/audit/build_scope.md) | 7219 | `543796e8052f38d85862655747b276cd35054caeadfd96bbe4bab9abf49f90f5` |
| [clean.log](raw/audit/clean.log) | 424 | `217f62a1867cdec708abe696438c64e9f2d06c3d9d71a7e9ce02be3fdbf70d18` |
| [clean_state.txt](raw/audit/clean_state.txt) | 375 | `9f37cee7113b879fd7caef22a65baacbd3d030b1b48b200d8108a7fb1378414a` |
| [collect_environment.py (in full audit ZIP: `audit-evidence/collect_environment.py`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 12629 | `79530984ceaf94ed10a06ce1e3a790704482497c55226a52939ca76fa4102a15` |
| [definition_source_files.txt](raw/audit/definition_source_files.txt) | 30167 | `daab5c364506b5a475f0c1a67327da0a00683bc8bd26fbe53cc53112d5a942dd` |
| [definitions.txt](raw/audit/definitions.txt) | 10809 | `70e8260e42fcd8f6b71296f99923d787f28e31a4a6448905eb3354db86ec4c78` |
| [dependency_direct.jsonl](raw/audit/dependency_direct.jsonl) | 42422 | `77e6e5c345d7c46e925a05034d4aacb1aa5754cf3ab08619cab749701c096e1c` |
| [dependency_edges.jsonl (in full audit ZIP: `audit-evidence/dependency_edges.jsonl`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 121250978 | `03f6590f8a6e0fa96a71475736f3489db52b2a6e699bb1606dbfed8662e09ddc` |
| [dependency_graph_review.json](raw/audit/dependency_graph_review.json) | 55051 | `560409df3b7a408284bec26d4ff3591d2ab3704b970782ea794520ca22822e57` |
| [dependency_nodes.jsonl (in full audit ZIP: `audit-evidence/dependency_nodes.jsonl`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 11958886 | `414f985a0f703d2c85c2ef8a006c7a626f81ccdc2b36d6d0fab548a9d0830448` |
| [dependency_provenance.txt](raw/audit/dependency_provenance.txt) | 156933 | `977ca8470a35d1ebaead55793c55f26d0683eb34ff6b6d8efc49dd1b3853eec6` |
| [dependency_source_map.json](raw/audit/dependency_source_map.json) | 46345 | `4110a8aba9d7fbe6a7b3d87d1c2959b2a57b44ec47a42f207ede4d0446dae02c` |
| [dependency_summary.json](raw/audit/dependency_summary.json) | 3967 | `01f57f9d2eb85509f6225efba1b51bc55ec4f538807d117ab73e35162024c6d7` |
| [dependency_summary.md](raw/audit/dependency_summary.md) | 20066 | `21cae9b01a9a4f942e6f9bbfdc1ec1acee7bf33fe1ef894424b1231262b31de2` |
| [dependency_trace.txt](raw/audit/dependency_trace.txt) | 1305 | `2d8c3f26ad7ccb0499e65a1a5d584ff6e4fe3105d19f493553fcbe898d154176` |
| [dependency_trace_run.txt](raw/audit/dependency_trace_run.txt) | 621 | `e4d8da09f6e817f7d92e03e40072d9fcaf3341a72162cd92ff6f6fd04d79dd8e` |
| [environment.txt](raw/audit/environment.txt) | 12310 | `bdb48a22064e9de79fe4f2ad5965b6ed26ad123c63cb61b71a050e5c1f087926` |
| [environment_collection_run.json](raw/audit/environment_collection_run.json) | 5748 | `5595c4c6018eb5534100492be7967b90e0882938a33dd55f25a9ca4f347dfd3c` |
| [final_placeholder_scan_run.log (in full audit ZIP: `audit-evidence/final_placeholder_scan_run.log`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 45937 | `4f704214b45b65ed2dd10b51f9d27d02256ad9d79587b206a8a6cc7dbac11233` |
| [final_report_generation.log (in full audit ZIP: `audit-evidence/final_report_generation.log`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 235 | `e34b2b7fd271c62f2a115ac53f932b698904b978fc93464943434224affc4e4d` |
| [generate_verification_report.py (in full audit ZIP: `audit-evidence/generate_verification_report.py`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 75494 | `a2827b0dd3fc77da66f1274a5f3cd7ec6e45810c89ed7ce530341cb21f09fb52` |
| [git_status.txt](raw/audit/git_status.txt) | 16590 | `27badfd08e38c682538da0d5a0bc223183683a4d4b1d611860f0fcd111ddb624` |
| [initial_failed_dependency_trace.txt](raw/audit/initial_failed_dependency_trace.txt) | 5261 | `a6cee4224338b3ea1a7aeaf198420305ceabbe55b48bd1322afc1dc17d8a4c2e` |
| [initial_failed_run_status.json](raw/audit/initial_failed_run_status.json) | 2562 | `4636a9acf8de993930199a0311c1550a40e6b7056d8bc0167095a3b3079a9edd` |
| [initial_failed_theorem_check.txt](raw/audit/initial_failed_theorem_check.txt) | 7580 | `7b50622c7b06910c5ecefc2175d35cf9b8c5c10e6371ae5145948ed2a7942c6c` |
| [initial_placeholder_audit.txt (in full audit ZIP: `audit-evidence/initial_placeholder_audit.txt`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 45940 | `7525e3ab04402de80e72a6411f08fd42e45595af3c84188ac3bb2003a7cfeb69` |
| [initial_placeholder_scan.json (in full audit ZIP: `audit-evidence/initial_placeholder_scan.json`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 291172 | `3e1e80db8176e34834b7679d28ffbbd6a57a58f12d39a1cfa0335a107e4cf1e1` |
| [kernel_dependency_summary.json](raw/audit/kernel_dependency_summary.json) | 7902 | `bf39f1bba6051ac91e14f405e312c96507d0cbdd5a64e9f6b0bdfdf0b527f9fe` |
| [local-source-inventory.txt (in full audit ZIP: `audit-evidence/local-source-inventory.txt`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 28798 | `2f67a6e6a7155b71da698cd33e3671a1b1cf83c00ad03bb8bb49f21f95b6a471` |
| [main_source_check.log](raw/audit/main_source_check.log) | 458 | `b6ce85faf1b1955ff22c0a1b0fc6c8d903655d8eb5da88c91b749592d49ce4e6` |
| [MainIdentity.before_formatter_fix.txt](raw/audit/MainIdentity.before_formatter_fix.txt) | 1117 | `71ccccc7a5ae37a5de129c200e32fa623b9762fc920e0e1d46a9a95a6cb70e63` |
| [MainIdentity.lean](raw/audit/MainIdentity.lean) | 1093 | `452913370a3c789e349e21525a7258879da254d35ea69c4f42dd7332fc2663c3` |
| [map_dependency_sources.ps1 (in full audit ZIP: `audit-evidence/map_dependency_sources.ps1`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 8611 | `fcf73a4e9e4cbc523980337e460e50fef93fb0900f8a8009ad02b07204295bda` |
| [package_audit.py (in full audit ZIP: `audit-evidence/package_audit.py`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 21851 | `084447300b70db3fa87c15979872a22904c360410c2b816462dd591e07fce783` |
| [placeholder_audit.txt](raw/audit/placeholder_audit.txt) | 45923 | `5ab6c3194538df708c74e4a7c0399818ae035e65d2fe3b81c98a65f005df6432` |
| [placeholder_scan.json](raw/audit/placeholder_scan.json) | 290059 | `d6ecda4953bd3d785a7a807daa8937fdbdc678aeed3eece4e7f04b4ebb4aab7d` |
| [placeholder_scan.py (in full audit ZIP: `audit-evidence/placeholder_scan.py`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 22365 | `03641e3117fbbb071e3b4b31c2793bcf808fd651877a6cff27558c922ad90cfe` |
| [placeholder_scan_run.log (in full audit ZIP: `audit-evidence/placeholder_scan_run.log`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 45954 | `df7839cdd8a49423502eef37c05eb5feeac7962719394dfddac7a0c41eb0f4e8` |
| [PrintAxioms.lean](raw/audit/PrintAxioms.lean) | 153 | `d7cdde0d7041a8c6021b7dda99865b4c415612e072b26fe0e650241eb8e5652f` |
| [PrintDefinitions.before_formatter_fix.txt](raw/audit/PrintDefinitions.before_formatter_fix.txt) | 732 | `92958b4afdd205d8b0e9d6baa1ff083caca30d169b6081c787f51353d7c362ed` |
| [PrintDefinitions.lean](raw/audit/PrintDefinitions.lean) | 708 | `795406e7f826673476d956b56fc6ac72707479ac5a0825a94076b466c8a91965` |
| [report_generator_preflight.json (in full audit ZIP: `audit-evidence/report_generator_preflight.json`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 3725 | `7869c459ce8d2300d8c5a7d6852db576fffdf405309808e8798c157bc4981923` |
| [report_generator_review_notes.md (in full audit ZIP: `audit-evidence/report_generator_review_notes.md`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 7198 | `4d81b7b595c00b71142f041253e452841fa7a0edb695d9b14c472aee1bdf518b` |
| [report_preflight_after_core.log (in full audit ZIP: `audit-evidence/report_preflight_after_core.log`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 519 | `452059c20d516b456f1c9ae96e3a81d3a33b51caa4899600ab85da967b275897` |
| [resume_after_formatter_fix.before_io_resume.txt](raw/audit/resume_after_formatter_fix.before_io_resume.txt) | 8151 | `fd63f1426a0894a4a30571218cee70c053453530ed5ad0962b640f55e656bda8` |
| [resume_after_formatter_fix.ps1](raw/audit/resume_after_formatter_fix.ps1) | 9361 | `c0b9dd80b23a20556f227d4cdfef5464be47f7e579dbb47120cb4845bbb40c3c` |
| [resumed_audit_failure.txt](raw/audit/resumed_audit_failure.txt) | 166 | `a916ad855980527b58632cb9cb7e8fd1a0dc29c2fa30451a7cff339386941620` |
| [review_dependency_graph.py (in full audit ZIP: `audit-evidence/review_dependency_graph.py`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 4685 | `c1ab37cf5aae0045a5592864f353bd481848af4f7c1ebf3f006a5ec879ba5510` |
| [run_additional_modules.ps1 (in full audit ZIP: `audit-evidence/run_additional_modules.ps1`)](downloads/Complemented_Subspace_Lean_Independent_Audit.PUBLIC.zip) | 6452 | `997533c6cd79b898559423d82da404b36ab7f0cf0c2ff4e687036427458e2d14` |
| [run_independent_audit.ps1](raw/audit/run_independent_audit.ps1) | 9159 | `e10dd6ab324998d25debf5c9d4e84d4e5154e06808dc87bfabb7a092c3f7c31c` |
| [run_status.json](raw/audit/run_status.json) | 5416 | `f502ff238516512cdd3844dcd5db8f24da47670d4ff1ff70eff56bb1fe0cd9f8` |
| [second_failed_run_status.json](raw/audit/second_failed_run_status.json) | 5331 | `514364e48d8a98e936605ffbd6506d0781424504f3b126c5884a3850ae6a8a05` |
| [source_hashes_after.json](raw/audit/source_hashes_after.json) | 39851 | `16f1a75202f685f2bbb3d7b7efef05290d43a631768e0e54236b44d15c87aef4` |
| [source_hashes_before.json](raw/audit/source_hashes_before.json) | 39851 | `16f1a75202f685f2bbb3d7b7efef05290d43a631768e0e54236b44d15c87aef4` |
| [source_unchanged.txt](raw/audit/source_unchanged.txt) | 80 | `c95a385da13df5e139a75062ac8df07c82bca4e2a38f62ec4400c00e897380c2` |
| [theorem_check.txt](raw/audit/theorem_check.txt) | 7481 | `35fc6a30112c50dabb58fb198ba6dd8f1b1fd952c3b592d1f2c7b9759083ba35` |
| [TraceDependencies.before_io_fix.txt](raw/audit/TraceDependencies.before_io_fix.txt) | 9910 | `da03c7b74ce33f55dd3a689a252903c11e106f7052fc6c12fafbeaa56f725c01` |
| [TraceDependencies.lean](raw/audit/TraceDependencies.lean) | 10130 | `da19376e92f4136f1f3b37e784f227286350137c242edfb0a6c4f91b04499e00` |
| [whole_project_axioms.txt](raw/audit/whole_project_axioms.txt) | 1089 | `834bc5b65a1d4c1aac99b6aef5bdcdce955094ee8490fb0941630c64f2d91086` |

## Appendix: full exact-definition compiler output

```text
WORKING DIRECTORY: LEAN_PROJECT
START UTC: 2026-09-05T23:14:50.8686342Z
COMMAND: & 'WORKSPACE\tmp\lean_library_definition_audit_2026-09-05\lean-4.34.0-rc2-windows\bin\lake.exe' '--no-cache' 'env' 'lean' '-j1' '-M8192' 'verification/independent-audit-2026-09-05/PrintDefinitions.lean'
TERMINAL OUTPUT:
def ComplementedSubspace.RealMainTheoremStatement : Prop :=
∀ (ρ : ℝ),
  LT.lt.{0} 0 ρ →
    ∃ a,
      TopologicalSpace.SeparableSpace.{0} ↥(ComplementedSubspace.Ambient a) ∧
        UniformConvexSpace.{0} ↥(ComplementedSubspace.Ambient a) ∧
          ComplementedSubspace.HasRealBanachLatticeOrder.{0} ↥(ComplementedSubspace.Ambient a) ∧
            ∃ P,
              Eq.{1} (ContinuousLinearMap.comp.{0, 0, 0, 0, 0, 0} P P) P ∧
                LT.lt.{0} (Norm.norm.{0} P) (HAdd.hAdd.{0, 0, 0} 1 ρ) ∧
                  LT.lt.{0}
                      (Norm.norm.{0}
                        (HSub.hSub.{0, 0, 0} (ContinuousLinearMap.id.{0, 0} ℝ ↥(ComplementedSubspace.Ambient a)) P))
                      (HAdd.hAdd.{0, 0, 0} 1 ρ) ∧
                    ComplementedSubspace.HasSeparatedRange.{0} P ∧
                      ComplementedSubspace.HasSeparatedRange.{0}
                        (HSub.hSub.{0, 0, 0} (ContinuousLinearMap.id.{0, 0} ℝ ↥(ComplementedSubspace.Ambient a)) P)
def ComplementedSubspace.HasSeparatedRange.{u_1} : {X : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} X] →
    [inst_1 : NormedSpace.{0, u_1} ℝ X] → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} ℝ) X X → Prop :=
fun {X} [NormedAddCommGroup.{u_1} X] [NormedSpace.{0, u_1} ℝ X] P =>
  LE.le.{0} (ComplementedSubspace.chiGL.{u_1} ↥(LinearMap.range.{0, 0, u_1, u_1} ↑P)) (ENorm.enorm.{u_1} P) ∧
    Eq.{1} (ComplementedSubspace.chiDPR.{u_1} ↥(LinearMap.range.{0, 0, u_1, u_1} ↑P)) Top.top.{0} ∧
      LE.le.{0}
          (ComplementedSubspace.chiGL.{u_1}
            (ContinuousLinearMap.{0, 0, u_1, 0} (RingHom.id.{0} ℝ) ↥(LinearMap.range.{0, 0, u_1, u_1} ↑P) ℝ))
          (ENorm.enorm.{u_1} P) ∧
        Eq.{1}
          (ComplementedSubspace.chiDPR.{u_1}
            (ContinuousLinearMap.{0, 0, u_1, 0} (RingHom.id.{0} ℝ) ↥(LinearMap.range.{0, 0, u_1, u_1} ↑P) ℝ))
          Top.top.{0}
def ComplementedSubspace.HasRealBanachLatticeOrder.{u_1} : (X : Type u_1) →
  [inst : NormedAddCommGroup.{u_1} X] → [NormedSpace.{0, u_1} ℝ X] → [CompleteSpace.{u_1} X] → Prop :=
fun X [NormedAddCommGroup.{u_1} X] [NormedSpace.{0, u_1} ℝ X] [CompleteSpace.{u_1} X] =>
  ∃ latticeOrder, IsOrderedAddMonoid.{u_1} X ∧ PosSMulMono.{0, u_1} ℝ X ∧ HasSolidNorm.{u_1} X
structure ComplementedSubspace.BlockParameters : Type
number of parameters: 0
fields:
  ComplementedSubspace.BlockParameters.dimension : ℕ → ℕ+
  ComplementedSubspace.BlockParameters.exponent : ℕ → ℝ
  ComplementedSubspace.BlockParameters.two_lt_exponent : ∀ (j : ℕ), LT.lt.{0} 2 (self.exponent j)
  ComplementedSubspace.BlockParameters.exponent_le_three : ∀ (j : ℕ), LE.le.{0} (self.exponent j) 3
  ComplementedSubspace.BlockParameters.exponent_antitone : Antitone.{0, 0} self.exponent
  ComplementedSubspace.BlockParameters.exponent_tendsto : Filter.Tendsto.{0, 0} self.exponent Filter.atTop.{0}
      (nhds.{0} 2)
constructor:
  ComplementedSubspace.BlockParameters.mk (dimension : ℕ → ℕ+) (exponent : ℕ → ℝ)
    (two_lt_exponent : ∀ (j : ℕ), LT.lt.{0} 2 (exponent j)) (exponent_le_three : ∀ (j : ℕ), LE.le.{0} (exponent j) 3)
    (exponent_antitone : Antitone.{0, 0} exponent)
    (exponent_tendsto : Filter.Tendsto.{0, 0} exponent Filter.atTop.{0} (nhds.{0} 2)) :
    ComplementedSubspace.BlockParameters
@[reducible] def ComplementedSubspace.Ambient : (a : ComplementedSubspace.BlockParameters) →
  AddSubgroup.{0} (PreLp.{0, 0} (ComplementedSubspace.Block a)) :=
fun a => lp.{0, 0} (ComplementedSubspace.Block a) 2
@[reducible] def ComplementedSubspace.Block : ComplementedSubspace.BlockParameters → ℕ → Type :=
fun a j => PiLp.{0, 0} (ENNReal.ofReal (a.exponent j)) fun x => ℝ
def ComplementedSubspace.chiGL.{u_1} : (Z : Type u_1) →
  [inst : NormedAddCommGroup.{u_1} Z] → [NormedSpace.{0, u_1} ℝ Z] → ENNReal :=
fun Z [NormedAddCommGroup.{u_1} Z] [NormedSpace.{0, u_1} ℝ Z] =>
  ⨆ V,
    ⨆ (_ : FiniteDimensional.{0, u_1} ℝ ↥V),
      ⨆ (_ : Ne.{u_1 + 1} V Bot.bot.{u_1}), ComplementedSubspace.lambdaGL.{u_1} Z V
def ComplementedSubspace.lambdaGL.{u_1} : (Z : Type u_1) →
  [inst : NormedAddCommGroup.{u_1} Z] → [inst_1 : NormedSpace.{0, u_1} ℝ Z] → Submodule.{0, u_1} ℝ Z → ENNReal :=
fun Z [NormedAddCommGroup.{u_1} Z] [NormedSpace.{0, u_1} ℝ Z] V =>
  ⨅ F, ComplementedSubspace.GLFactorization.cost.{u_1} F
structure ComplementedSubspace.GLFactorization.{u_1} {Z : Type u_1} [NormedAddCommGroup.{u_1} Z]
  [NormedSpace.{0, u_1} ℝ Z] (V : Submodule.{0, u_1} ℝ Z) : Type u_1
number of parameters: 4
fields:
  ComplementedSubspace.GLFactorization.dimension.{u_1} : ℕ
  ComplementedSubspace.GLFactorization.auxNorm.{u_1} : Seminorm.{0, 0} ℝ
      (Fin (ComplementedSubspace.GLFactorization.dimension.{u_1} self) → ℝ)
  ComplementedSubspace.GLFactorization.positive_definite.{u_1} : ∀
      (x : Fin (ComplementedSubspace.GLFactorization.dimension.{u_1} self) → ℝ),
      Eq.{1} ((ComplementedSubspace.GLFactorization.auxNorm.{u_1} self) x) 0 → Eq.{1} x 0
  ComplementedSubspace.GLFactorization.unconditional.{u_1} : ∀
      (θ x : Fin (ComplementedSubspace.GLFactorization.dimension.{u_1} self) → ℝ),
      (∀ (i : Fin (ComplementedSubspace.GLFactorization.dimension.{u_1} self)), LE.le.{0} (Norm.norm.{0} (θ i)) 1) →
        LE.le.{0} ((ComplementedSubspace.GLFactorization.auxNorm.{u_1} self) fun i => HMul.hMul.{0, 0, 0} (θ i) (x i))
          ((ComplementedSubspace.GLFactorization.auxNorm.{u_1} self) x)
  ComplementedSubspace.GLFactorization.a.{u_1} : LinearMap.{0, 0, u_1, 0} (RingHom.id.{0} ℝ) (↥V)
      (Fin (ComplementedSubspace.GLFactorization.dimension.{u_1} self) → ℝ)
  ComplementedSubspace.GLFactorization.b.{u_1} : LinearMap.{0, 0, 0, u_1} (RingHom.id.{0} ℝ)
      (Fin (ComplementedSubspace.GLFactorization.dimension.{u_1} self) → ℝ) Z
  ComplementedSubspace.GLFactorization.factorizes.{u_1} : Eq.{u_1 + 1}
      (ComplementedSubspace.GLFactorization.b.{u_1} self ∘ₗ ComplementedSubspace.GLFactorization.a.{u_1} self)
      (Submodule.subtype.{0, u_1} V)
  ComplementedSubspace.GLFactorization.aBound.{u_1} : NNReal
  ComplementedSubspace.GLFactorization.bBound.{u_1} : NNReal
  ComplementedSubspace.GLFactorization.bound_a.{u_1} : ∀ (x : ↥V),
      LE.le.{0}
        ((ComplementedSubspace.GLFactorization.auxNorm.{u_1} self)
          ((ComplementedSubspace.GLFactorization.a.{u_1} self) x))
        (HMul.hMul.{0, 0, 0} (↑(ComplementedSubspace.GLFactorization.aBound.{u_1} self)) (Norm.norm.{u_1} x))
  ComplementedSubspace.GLFactorization.bound_b.{u_1} : ∀
      (x : Fin (ComplementedSubspace.GLFactorization.dimension.{u_1} self) → ℝ),
      LE.le.{0} (Norm.norm.{u_1} ((ComplementedSubspace.GLFactorization.b.{u_1} self) x))
        (HMul.hMul.{0, 0, 0} (↑(ComplementedSubspace.GLFactorization.bBound.{u_1} self))
          ((ComplementedSubspace.GLFactorization.auxNorm.{u_1} self) x))
constructor:
  ComplementedSubspace.GLFactorization.mk.{u_1} {Z : Type u_1} [NormedAddCommGroup.{u_1} Z] [NormedSpace.{0, u_1} ℝ Z]
    {V : Submodule.{0, u_1} ℝ Z} (dimension : ℕ) (auxNorm : Seminorm.{0, 0} ℝ (Fin dimension → ℝ))
    (positive_definite : ∀ (x : Fin dimension → ℝ), Eq.{1} (auxNorm x) 0 → Eq.{1} x 0)
    (unconditional :
      ∀ (θ x : Fin dimension → ℝ),
        (∀ (i : Fin dimension), LE.le.{0} (Norm.norm.{0} (θ i)) 1) →
          LE.le.{0} (auxNorm fun i => HMul.hMul.{0, 0, 0} (θ i) (x i)) (auxNorm x))
    (a : LinearMap.{0, 0, u_1, 0} (RingHom.id.{0} ℝ) (↥V) (Fin dimension → ℝ))
    (b : LinearMap.{0, 0, 0, u_1} (RingHom.id.{0} ℝ) (Fin dimension → ℝ) Z)
    (factorizes : Eq.{u_1 + 1} (b ∘ₗ a) (Submodule.subtype.{0, u_1} V)) (aBound bBound : NNReal)
    (bound_a : ∀ (x : ↥V), LE.le.{0} (auxNorm (a x)) (HMul.hMul.{0, 0, 0} (↑aBound) (Norm.norm.{u_1} x)))
    (bound_b :
      ∀ (x : Fin dimension → ℝ), LE.le.{0} (Norm.norm.{u_1} (b x)) (HMul.hMul.{0, 0, 0} (↑bBound) (auxNorm x))) :
    ComplementedSubspace.GLFactorization.{u_1} V
def ComplementedSubspace.chiDPR.{u_1} : (Z : Type u_1) →
  [inst : NormedAddCommGroup.{u_1} Z] → [NormedSpace.{0, u_1} ℝ Z] → ENNReal :=
fun Z [NormedAddCommGroup.{u_1} Z] [NormedSpace.{0, u_1} ℝ Z] =>
  ⨆ V,
    ⨆ (_ : FiniteDimensional.{0, u_1} ℝ ↥V),
      ⨆ (_ : Ne.{u_1 + 1} V Bot.bot.{u_1}), ComplementedSubspace.lambdaDPR.{u_1} Z V
def ComplementedSubspace.lambdaDPR.{u_1} : (Z : Type u_1) →
  [inst : NormedAddCommGroup.{u_1} Z] → [inst_1 : NormedSpace.{0, u_1} ℝ Z] → Submodule.{0, u_1} ℝ Z → ENNReal :=
fun Z [NormedAddCommGroup.{u_1} Z] [NormedSpace.{0, u_1} ℝ Z] V =>
  ⨅ F,
    ⨅ (_ : LE.le.{u_1} V F),
      ⨅ (_ : FiniteDimensional.{0, u_1} ℝ ↥F), ComplementedSubspace.unconditionalConstant.{u_1} ↥F
def ComplementedSubspace.unconditionalConstant.{u_2} : (E : Type u_2) →
  [inst : NormedAddCommGroup.{u_2} E] → [NormedSpace.{0, u_2} ℝ E] → ENNReal :=
fun E [NormedAddCommGroup.{u_2} E] [NormedSpace.{0, u_2} ℝ E] =>
  ⨅ n, ⨅ b, ComplementedSubspace.unconditionalBasisConstant.{u_2} b
def ComplementedSubspace.unconditionalBasisConstant.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] →
    [inst_1 : NormedSpace.{0, u_1} ℝ E] → {n : ℕ} → Module.Basis.{0, 0, u_1} (Fin n) ℝ E → ENNReal :=
fun {E} [NormedAddCommGroup.{u_1} E] [NormedSpace.{0, u_1} ℝ E] {n} b =>
  Max.max.{0} 1
    (⨆ θ,
      ⨆ (_ : ∀ (i : Fin n), LE.le.{0} (Norm.norm.{0} (θ i)) 1),
        ENorm.enorm.{u_1} (ComplementedSubspace.basisMultiplier.{u_1} b θ))
def ComplementedSubspace.basisMultiplier.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] →
    [inst_1 : NormedSpace.{0, u_1} ℝ E] →
      {n : ℕ} →
        Module.Basis.{0, 0, u_1} (Fin n) ℝ E →
          (Fin n → ℝ) → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} ℝ) E E :=
fun {E} [NormedAddCommGroup.{u_1} E] [NormedSpace.{0, u_1} ℝ E] {n} b θ =>
  Module.Basis.constrL.{0, u_1, u_1, 0} b fun i => HSMul.hSMul.{0, u_1, u_1} (θ i) (b i)
EXIT CODE: 0
END UTC: 2026-09-05T23:15:29.7061797Z
```
