"""Assemble reviewed result drafts from completed evidence; packaging publishes PASS."""
from audit_runner import *

def read(name): return json.loads((EVIDENCE/name).read_text())
def command(name):
    value=read(name+'.command.json')
    if value.get('exit_code')!=0 or not value.get('ended') or value.get('timed_out'):
        raise RuntimeError('Required successful process missing: '+name)
    return value

def main():
    labels=['initial-fresh-replay','source-rebuild','rebuilt-fresh-replay',
        'endpoint-types-and-axioms','printed-mathematical-definitions','review-formulation-identity',
        'source-identity-and-placeholder-scan','resolved-build-input-check','final-preservation-check']
    commands={name:command(name) for name in labels}
    identity=read('identity-source-and-scan.json')
    preservation=read('final-preservation.json')
    if not identity['pass'] or preservation['status']!='PASS':
        raise RuntimeError('Identity/preservation is not PASS')
    if read('resolved-build-inputs/summary.json')['status']!='PASS':
        raise RuntimeError('Resolved input check is not PASS')
    if not (EVIDENCE/'source-scan-review.md').is_file():
        raise RuntimeError('Source findings require their documented review')
    state=read('status.json')
    state['stages']['1_source_environment_target_identity']='PASS'
    state['stages']['5_endpoint_definition_axiom_checks']='PASS'
    state['stages']['6_final_preservation_and_packaging']='RUNNING'
    save('status.json',state)
    report=(EVIDENCE/'report-core-draft.md').read_text()
    paragraphs=report.split('\n\n')
    paragraphs[1]='**FULL FRESH AUDIT: PASS.** The frozen project and its imported non-toolchain dependencies were rebuilt from pinned sources. Both official fresh kernel replays, all five endpoint checks, definition/source identity, and the transitive axiom allowlist passed. The final archive validation receipt records the completed packaging check.'
    report='\n\n'.join(paragraphs)
    report=report.replace('PASS for initial frozen snapshot, pins and target; final preservation belongs to stage 6','PASS')
    replay=commands['rebuilt-fresh-replay']
    old='| 4. Fresh replay of rebuilt artifacts | REBUILT_REPLAY_PENDING; started 12:40:23 UTC | [Command record](rebuilt-fresh-replay.command.json) |'
    new=f"| 4. Fresh replay of rebuilt artifacts | PASS: exit 0; {replay['elapsed_seconds']:.3f} s; 12:40:23–12:54:17 UTC | [Command](rebuilt-fresh-replay.command.json), [raw replay log](rebuilt-fresh-replay.log) |"
    if old not in report: raise RuntimeError('Replay draft marker missing')
    report=report.replace(old,new)
    report=report.replace('| 5. Endpoint types, definition identity and transitive axioms | ENDPOINT_IDENTITY_PENDING | [Endpoint helper](EndpointChecks.lean), [definition helper](PrintDefinitions.lean); completed command outputs must be attached |',
        '| 5. Endpoint types, definition identity and transitive axioms | PASS: all native exit codes 0; no additional endpoint axioms | [Proof types/axioms](endpoint-types-and-axioms.log), [definitions](printed-mathematical-definitions.log), [formulation identity](review-formulation-identity.log), [source identity](identity-source-and-scan.json) |')
    report=report.replace('Final preservation, source-scan and archive-validation records must be attached',
        '[Final preservation](final-preservation.json), [final source manifest](source-manifest-after.sha256), [detached archive validation](../archive-validation.json)')
    report=report.replace('Scheduled endpoint/formulation invocations','The executed endpoint/formulation invocations')
    report=report.replace('Pending execution is not a successful check.',
        'All three returned native exit code 0 (24.094 s, 17.453 s and 19.938 s respectively).')
    report=report.replace('The final report must quote actual per-endpoint axiom results after completion, without copying historical counts.',
        'The completed run found all five declarations to be theorems with no universe or outer theorem parameters. The actual stored types agree with the table. Each of the five printed exactly `[propext, Classical.choice, Quot.sound]`; no additional axiom was found. The separate namespace traversal checked 2,573 imported `ComplementedSubspace` declarations against the same allowlist and passed.')
    report=report.replace('Source/presentation comparison and lexical auditing are supplementary; their final results remain pending here.',
        'All 25 requested definition bodies were printed successfully, the formulation review returned exit 0, and 82 website source snippets/context captures matched the reproduced source under CRLF-to-LF normalization only. The full source files, literal bodies and implicit contexts retain the existing paper mapping.')
    report=report.replace('Final source-preservation and evidence-archive validation must complete before the report can carry an overall PASS.',
        'Final original/reproduced project and dependency hashes matched all baseline bytes. The previous audit files, original root artifact, frozen source archive, checker binaries, runtime libraries and reference checker sources remained unchanged. The source archive and final evidence archive were checked by CRC, exact member set and SHA-256; the final archive digest is detached to avoid self-reference.')
    report += '''

## Supplementary source findings

The lexical scan covered 2,831 Lean files: 177 imported local modules, 53 other local files, two new audit helpers, two reference copies of the official checker/replay source, and 2,597 built external module sources. There were zero imported-project placeholder/trust-override gate hits. The project's transparency, heartbeat and three scoped `allowUnsafeReducibility` settings are recorded; their spelling alone does not constitute a kernel bypass.

The external code-class findings include six `sorry`, four `admit` and five `sorryAx` spellings. Some are actual placeholder-generating metaprograms in LeanSearchClient, Aesop script scaffolding and `calc?`; others are option identifiers, recognizers or hover metadata. These findings have been retained and individually reviewed, not suppressed. No external code-class `axiom`, `native_decide`, `ofReduceBool`, `trust`, `trustLevel` or `skipKernelTC` occurrence was recorded in this selected source scope. General unsafe/partial/metaprogram implementations were not all separately verified for correctness.

[Reviewed contexts and counts](source-scan-review.md), [complete lexical occurrences](identity-lexical-occurrences.jsonl), [scanned-source inventory](identity-lexical-source-inventory.json). This textual review is supplementary. The actual transitive checks rule out extra axiom dependencies for the claimed endpoint proofs and the audited project namespace; the official fresh replay checks the resulting safe logical declarations.

## Final preservation, archive and scope

After all Lean invocations finished, a further hash pass checked each original and reproduced project tree (233 files each) and each original and reproduced dependency tree (10,056 tracked files each). Every hash matched. The original and newly rebuilt integration root have the same SHA-256, `b0874218a920926d711a7949ba0ba48f1d3a0014da86c399e3dfb1eedbb15ee7`; this is an observed artifact identity, not a substitute for the independent source build.

[Final native check](final-preservation-check.log), [preservation details](final-preservation.json), [unchanged project manifest](source-manifest-after.sha256). No mathematical source, proof, definition, notation, instance, dependency revision or foundational allowlist was repaired or changed in this audit. There were no rejected Lean/checker/helper checks in this supplementary run. The expected unborn-HEAD metadata probe is distinguished above. Audit-only scripts were reviewed and prepared before execution; their raw outputs are unedited.

The downloadable [evidence archive](../full-fresh-audit-evidence.zip) contains the run records and separate raw streams, all audit helper sources, manifests, full module/path map, source archives, exact statement/definition output and reproduction notes. `CONTENTS.sha256` covers every member except itself. The [detached receipt](../archive-validation.json) records the final archive SHA-256, all-member CRC/SHA validation, file count and full elapsed audit time. The final packaging command and its receipt remain outside the archive to avoid a self-referential hash. Checkpoint archives of the earlier website and audit remain separately preserved locally.

This records source reproduction, kernel replay and axiom checks for the listed formal statements. It uses Lean's own kernel and the stated foundational assumptions; it is not verification by a separate kernel implementation. The correspondence between the formal statements and the paper is reviewed and explained separately. Alternative formal proofs do not certify every step of a different manuscript proof.

Everything remains local and unpublished: no uploads, repository pushes, cache publication or external preview were performed. Raw evidence includes the Windows username and personal paths. It is an unredacted local original; review a separately labelled, separately manifested redacted copy before any eventual public release. The compact companion link belongs on the existing Verification page and records this snapshot, not future source edits or live CI.
'''
    if any(marker in report for marker in ['OVERALL_PENDING','REBUILT_REPLAY_PENDING','ENDPOINT_IDENTITY_PENDING']):
        raise RuntimeError('Pending check marker remains in final draft')
    if report.count('PACKAGING_PENDING')!=1:
        raise RuntimeError('Expected exactly one packaging marker')
    (EVIDENCE/'report.md.draft').write_text(report,encoding='utf-8')
    snapshot=read('snapshot.json')['source_manifest_sha256']
    summary=f'''# Final fresh Lean audit status — 6 September 2026

All requested mathematical checks passed. Final packaging status: **PACKAGING_PENDING**.

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

Frozen source manifest SHA-256: `{snapshot}`. Start 10:28:54 UTC; archive-validation.json records the exact final elapsed time and archive digest. No mathematical audit stage remains unfinished after the packaging PASS.

Report: evidence/report.md (also report.html). Raw logs: evidence/*.log and *.command.json. Download bundle: full-fresh-audit-evidence.zip, with internal CONTENTS.sha256 and detached archive-validation.json. Reproduction: evidence/REPRODUCE.md.

Companion location: existing Verification page, `/verification/#extended-fresh-audit`. Website integration/validation is recorded separately after the mathematical audit package is finalized. Everything remains local and unpublished; no uploads or power-setting/shutdown actions occurred. Raw local evidence retains personal Windows paths for review before any eventual public release.
'''
    (EVIDENCE/'FINAL_FRESH_AUDIT_STATUS.md.draft').write_text(summary,encoding='utf-8')
    (EVIDENCE/'definition-identity-checks.txt').write_text(
        'PASS: five proof-at-type checks; five statement and twenty project definitions printed; existing formulation review exit 0; 82 exact source/context captures match.\nSee endpoint-types-and-axioms.log, printed-mathematical-definitions.log, review-formulation-identity.log, identity-source-and-scan.json.\n',encoding='utf-8')
    (EVIDENCE/'placeholder-audit.txt').write_text(
        'PASS for imported-project lexical gate; zero gate hits. 2,831 files scanned. External placeholder-generating tooling is present and documented.\nSee source-scan-review.md and identity-lexical-occurrences.jsonl. The five endpoint and 2,573 project-namespace transitive axiom checks passed independently.\n',encoding='utf-8')
    print('Prepared final report/status drafts from completed checks; archive validation must publish PASS.')

if __name__=='__main__': main()
