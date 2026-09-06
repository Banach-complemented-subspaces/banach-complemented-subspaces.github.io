# Scheduled audit helpers: bounded independent review

Reviewed the copies of `EndpointChecks.lean`, `PrintDefinitions.lean` and `check_identity_and_scan.py` in `output/full_fresh_audit_2026-09-06_102854/evidence`, against `Downloads/CODEX_FULL_FRESH_LEAN_AUDIT_AND_WEBSITE.txt`, the frozen declarations, the preserved lexical helper and matching toolchain source. This was static, read-only inspection. No Lean invocation, lexer self-test, source scan, Git command or helper execution was performed; no scheduled helper was modified.

## Findings requiring report/runner attention

1. **Distinguish tooling incompletion from rejection.** `check_identity_and_scan.py` currently funnels a missing source, permission error, Git timeout/launch error, lexing limitation or generic helper exception into `REPORT['failures']`; `finish()` labels every such result `FAILED CHECK`. Section 8 of the user brief requires `NOT COMPLETED` for unavailable source, resource/permission limits or unresolved tooling. Keep genuine hash/snippet mismatches and identified project gate violations as failed checks, but give infrastructure/coverage failures an incomplete status, either in this helper before its run or in the enclosing stage classifier. Preserve the actual diagnostic and command outcome in either case. The existing nonzero exit behavior is appropriate; nonzero alone does not determine the mathematical interpretation.

2. **Endpoint types are checked by elaborated ascription; exact stored-expression identity is not enforced.** The five `#check (endpoint : expected)` commands are correct, and the loop checks `.thmInfo`, no universe parameters and no top-level `forall`, then logs the stored type. It does not compare `info.type` with an expected expression. This meets the explicit proof-at-type check in the user brief for the current frozen sources, but the report should not call it an exact syntactic stored-type comparison equivalent to the older real-main `MainIdentity.lean` guard. If that stronger check is desired, add an audit-only expected-type comparison and elaborate the real unconditional type application rather than treating it as a bare constant. Do not unfold the named statement before the no-parameter check: its intended mathematical quantifiers are inside that statement definition.

3. **Artifact-to-source mapping assumes default library source directories.** The scanner maps each `.lake/build/lib/lean/A/B.olean` to package-root `A/B.lean`. That is appropriate for the ordinary mathematical libraries inspected. Some pinned package executable targets declare `srcDir = "scripts"` (Batteries and Mathlib). They normally are not required by this root's mathematical import build; if an artifact from such a target is present, the mapper can report missing/untracked source even when a legitimate source exists under its configured `srcDir`. Treat that as incomplete source mapping, not a mathematical failure. Do not silently omit such artifacts; resolve their actual source from pinned configuration if encountered.

No definite immediate Lean API or ordinary-path runtime blocker was found in the three scheduled helpers after the output-prefix correction. This is not a successful execution result.

## Five endpoint expectations

All five ascriptions in `EndpointChecks.lean` exactly match the frozen source headers:

| Endpoint suffix under `ComplementedSubspace` | Expected type under the same namespace |
|---|---|
| `realMainTheorem` | `RealMainTheoremStatement` |
| `realCorollary` | `RealCorollaryStatement` |
| `realUnconditionalCorollary` | `UnconditionalCorollaryStatement ℝ` |
| `realSeparableNonprimarity` | `SeparableNonprimarityStatement` |
| `complexCorollary` | `ComplexCorollaryStatement` |

The root imports their three source modules at `ComplementedSubspace.lean:75–77`. The helper prints each endpoint's transitive axioms and enforces precisely `propext`, `Classical.choice`, `Quot.sound`; a subset is accepted. It also runs the existing namespace-wide allowlist loop. `Lean.Expr.isForall` exists in the pinned source at `Lean/Expr.lean:893`; the environment/axiom loop follows previously used local audit APIs. The loop does not insert mathematical declarations or assumptions. Its namespace count is a count of matching imported names, not a count of all declarations replayed by `leanchecker` or all local origin-module declarations.

## Actual printed definitions

`PrintDefinitions.lean` imports the integration root and requests fully qualified, universe-explicit output. It lists exactly the five statement definitions plus the twenty project definitions in the current site catalogue:

- Statements: real main, real corollary, generic unconditional corollary, complex corollary, separable nonprimarity.
- Finite/local structure: `basisMultiplier`, `unconditionalBasisConstant`, `unconditionalConstant`, `lambdaDPR`, `chiDPR`, `GLFactorization`, `GLFactorization.cost`, `lambdaGL`, `chiGL`.
- Space/range data: `BlockParameters`, `Block`, `Ambient`, `HasRealBanachLatticeOrder`, `HasSeparatedRange`.
- Corollary data/predicates: `BanachModel`, `HasUnconditionalSchauderBasis`, `IsOneUnconditional`, `HasOneUnconditionalSchauderBasis`, `IsSuperreflexiveByRenorming`, `IsIsomorphicToRealBanachLattice`.

Every requested declaration name exists in the frozen source. `#print` gives the actual definitions but is not itself an equality proof against an English statement. The scheduled `MainTheoremReview.lean` run supplies the existing real-main `rfl` formulation checks separately.

## Lexer interface and classification

The scanner uses the preserved helper's actual interface correctly: `lex(text)` returns `(clean, kinds, constructs, issues)`; `imports_from(clean)` returns `(imports, errors)`; `line_info(text, offset)` returns `(line, column, source)`; `scanner_self_test()` is a callable returning its status after assertions; `TOKEN_RE` is available. These functions are defined at module level. Importing an evidence copy under a non-`__main__` name leaves the old `main()` inactive, and bytecode output is disabled while loading it. No old scan writers are called.

The corrected `output()` adds `identity-` centrally when absent, so unprefixed calls now agree with the final existence guard and advertised filenames. Existing prefixes are preserved. Native Git records now contain actual cwd/argv, start/end, elapsed, PID, returned exit code, full text streams and hashed raw-byte streams; timeout handling kills and waits for that child before recording its exit code. Launch failures correctly have no process exit code.

The project gate applies only within the syntactic local import closure of the integration root. Unrelated local/audit files and fresh evidence Lean helpers receive separate labels. Comments, strings and executable-token classes remain separate. External module source is selected by actual isolated `.olean` artifacts and checked against copied tracked-source manifests; unsafe/meta/native/opaque/axiom-related external tokens are reported rather than automatically rejected. As documented, syntax quotations remain conservatively classified as code, so token counts are not counts of mathematical axioms. Toolchain core sources are outside this supplementary source scan; the separately documented official fresh replay determines their logical replay treatment.

The imported-project gate conservatively flags any executable spelling of a trust/skip-kernel token, including a hypothetical explicit harmless setting. Current reviewed project settings concern elaboration/reducibility rather than those gated tokens. Any actual hit needs the recorded source context and semantic review; do not equate token presence with a theorem being false.

## Newlines, identities and limits

The website comparator matches the two actual capture conventions:

- `definitions.json` snippets and contexts preserve complete selected source lines, including their terminal line separators.
- `evidence.json` endpoint/statement literals and contexts were produced by joining selected source lines without a final separator.

The helper explicitly reconstructs each convention and normalizes CRLF to LF on both sides; it does not strip indentation, spaces or code. Relative project paths and `.lake/packages/mathlib/...` paths are resolved against the reproduced tree rather than the original absolute references. This is the right distinction for the current data. `splitlines()` also recognizes uncommon Unicode line separators, so its strict newline-only description assumes the ordinary LF/CRLF source convention used by the observed captures; no new whole-source newline scan was run for this review.

The helper checks the 233-entry original and reproduction manifests against current bytes, both original/copied dependency tracked-file sets and hashes, and repeats source hashing after the scan. It also checks the source-manifest hash recorded in `snapshot.json`. It does not establish initial clean-state/cache isolation, fresh build success, kernel replay success, the final endpoint axiom result or manuscript correspondence; those need their distinct scheduled evidence. The website files themselves are read-only inputs but are not snapshotted/rehashed at the end by this helper, so their identity claim is about the content read at the time of the check. A final packaged website/content manifest can provide the additional stable presentation snapshot.
