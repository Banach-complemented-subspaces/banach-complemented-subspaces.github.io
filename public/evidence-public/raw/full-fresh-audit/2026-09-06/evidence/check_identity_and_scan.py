"""Supplementary source identity / lexical audit. Run AFTER the isolated build.

No Lean/build commands are run. Only the fresh audit's evidence sibling is written.
Library implementation/unsafe/native hits are reported for review, not rejected en masse.
This source scan does not certify elaboration, kernel replay, or manuscript interpretation.
"""
from __future__ import annotations

from collections import Counter, deque
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
import time
import traceback

WORKSPACE = Path(r'WORKSPACE')
AUDIT = WORKSPACE / 'output/full_fresh_audit_2026-09-06_102854'
REPRO = AUDIT / 'reproduction'
EVIDENCE = AUDIT / 'evidence'
ORIGINAL = WORKSPACE / 'output/lean_trial_2026-09-05'
SITE = WORKSPACE / 'output/complemented-subspace-companion'
OLD_LEXER = ORIGINAL / 'verification/independent-audit-2026-09-05/placeholder_scan.py'
GIT = Path(r'C:\Program Files\Git\cmd\git.exe')
EXPECTED_PROJECT_COUNT = 233
BLOCKED_PROJECT_TOKENS = {
    'sorry', 'sorryAx', 'admit', 'admitted', 'skipKernelTC',
    'debug.skipKernelTC', 'trust', 'trustLevel',
}
REPORT = {'started_utc': None, 'pass': False, 'failures': [], 'warnings': []}
NATIVE_COMMANDS = []


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def failure(kind, **details):
    REPORT['failures'].append({'kind': kind, **details})


def local_path(root, relative):
    """Reject absolute/traversing paths and paths resolving outside the declared root."""
    rel = PurePosixPath(str(relative).replace('\\', '/'))
    if rel.is_absolute() or '..' in rel.parts or any(':' in p for p in rel.parts):
        raise ValueError(f'Unsafe relative source path: {relative!r}')
    root = root.resolve(strict=True)
    path = root.joinpath(*rel.parts)
    resolved = path.resolve(strict=False)
    if not resolved.is_relative_to(root):
        raise ValueError(f'Source resolves outside declared root: {path}')
    for candidate in [path, *path.parents]:
        if candidate == root.parent:
            break
        if candidate.exists() and is_reparse(candidate):
            raise ValueError(f'Source path traverses a reparse point: {candidate}')
    return path


def is_reparse(path):
    info = path.lstat()
    return path.is_symlink() or bool(getattr(info, 'st_file_attributes', 0) &
                                    getattr(stat, 'FILE_ATTRIBUTE_REPARSE_POINT', 0))


def output(name):
    """Every output must be a direct child of the fixed new evidence directory."""
    if not EVIDENCE.is_dir() or is_reparse(EVIDENCE) or is_reparse(AUDIT):
        raise ValueError('Evidence directory is absent or passes through a reparse point')
    if EVIDENCE.resolve(strict=True).parent != AUDIT.resolve(strict=True):
        raise ValueError('Evidence is not the reproduction sibling in the fixed audit root')
    if Path(name).name != name:
        raise ValueError(f'Invalid evidence output name: {name!r}')
    if not name.startswith('identity-'):
        name = 'identity-' + name
    path = EVIDENCE / name
    if path.exists() and is_reparse(path):
        raise ValueError(f'Output is a reparse point: {path}')
    if path.resolve(strict=False).parent != EVIDENCE.resolve(strict=True):
        raise ValueError(f'Output escaped evidence directory: {path}')
    return path


def save(name, value):
    output(name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


def read_manifest(name):
    path = EVIDENCE / name
    records = {}
    for number, line in enumerate(path.read_text(encoding='utf-8-sig').splitlines(), 1):
        if not line:
            continue
        match = re.fullmatch(r'([0-9a-fA-F]{64})  (.+)', line)
        if not match:
            raise ValueError(f'Malformed manifest line {name}:{number}')
        digest, rel = match.groups()
        rel = rel.replace('\\', '/')
        if rel in records:
            raise ValueError(f'Duplicate manifest entry: {name}: {rel}')
        # Validate relative spelling even when the root file may be missing.
        local_path(REPRO, rel)
        records[rel] = digest.lower()
    if not records:
        raise ValueError(f'Empty manifest: {name}')
    return records


def check_manifest(label, root, before, expected_count=None):
    if expected_count is not None and len(before) != expected_count:
        failure('manifest_count', label=label, expected=expected_count, actual=len(before))
    after, bad = {}, []
    for rel, wanted in before.items():
        try:
            path = local_path(root, rel)
            actual = sha(path)
            after[rel] = actual
            if actual != wanted:
                bad.append({'path': rel, 'expected': wanted, 'actual': actual})
        except (OSError, ValueError) as exc:
            bad.append({'path': rel, 'error': str(exc)})
    output(f'identity-{label}-manifest-after.sha256').write_text(
        ''.join(f'{digest}  {rel}\n' for rel, digest in after.items()), encoding='utf-8')
    if bad:
        failure('manifest_mismatch', label=label, mismatches=bad)
    return {'label': label, 'root': str(root), 'expected_files': len(before),
            'observed_files': len(after), 'mismatch_count': len(bad), 'matches': not bad}, after


def tracked_paths(root):
    env = os.environ.copy()
    env['GIT_OPTIONAL_LOCKS'] = '0'
    argv = [str(GIT), 'ls-files', '-z']
    record = {'sequence': len(NATIVE_COMMANDS) + 1, 'cwd': str(root.resolve(strict=True)),
              'executable': str(GIT), 'arguments': argv[1:], 'argv': argv,
              'command_line': subprocess.list2cmdline(argv),
              'started_utc': now(), 'ended_utc': None, 'elapsed_seconds': None,
              'actual_exit_code': None, 'timeout_seconds': 60, 'timed_out': False,
              'environment_overrides': {'GIT_OPTIONAL_LOCKS': '0'},
              'stdout': '', 'stderr': '', 'stdout_encoding': 'utf-8',
              'stderr_encoding': 'utf-8', 'status': 'RUNNING'}
    NATIVE_COMMANDS.append(record)
    save('native-commands.json', NATIVE_COMMANDS)
    started = time.monotonic()
    stdout = stderr = b''
    process = None
    try:
        process = subprocess.Popen(argv, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   env=env, creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0))
        record['pid'] = process.pid
        save('native-commands.json', NATIVE_COMMANDS)
        try:
            stdout, stderr = process.communicate(timeout=60)
        except subprocess.TimeoutExpired:
            process.kill()
            stdout, stderr = process.communicate()
            record['actual_exit_code'] = process.returncode
            raise
        record['actual_exit_code'] = process.returncode
        record['status'] = 'PASS' if process.returncode == 0 else 'FAILED COMMAND'
    except subprocess.TimeoutExpired as exc:
        record.update(timed_out=True, status='TIMED OUT', error=str(exc),
                      exit_code_note='Actual exit code is from the child after timeout termination and wait, not a successful command completion')
        raise
    except OSError as exc:
        record.update(status='LAUNCH ERROR' if process is None else 'PROCESS IO ERROR', error=str(exc))
        raise
    finally:
        record.update(ended_utc=now(), elapsed_seconds=time.monotonic() - started,
                      stdout=stdout.decode('utf-8', 'replace'),
                      stderr=stderr.decode('utf-8', 'replace'),
                      stdout_bytes=len(stdout), stderr_bytes=len(stderr),
                      stdout_sha256=hashlib.sha256(stdout).hexdigest(),
                      stderr_sha256=hashlib.sha256(stderr).hexdigest())
        # Preserve raw bytes too, including NUL-separated tracked file names.
        stdout_name = f'native-{record["sequence"]:03d}.stdout.bin'
        stderr_name = f'native-{record["sequence"]:03d}.stderr.bin'
        output(stdout_name).write_bytes(stdout)
        output(stderr_name).write_bytes(stderr)
        record['stdout_raw_file'] = output(stdout_name).name
        record['stderr_raw_file'] = output(stderr_name).name
        save('native-commands.json', NATIVE_COMMANDS)
    if process.returncode:
        raise RuntimeError(f'git ls-files failed for {root}: {stderr.decode("utf-8", "replace")}')
    return {x.replace('\\', '/') for x in stdout.decode('utf-8').split('\0') if x}


def check_dependency_tracked_sets(baseline, revisions):
    rows = []
    expected_packages = {r['name'] for r in revisions}
    actual_packages = {p.split('/', 1)[0] for p in baseline}
    if actual_packages != expected_packages:
        failure('dependency_manifest_package_set', expected=sorted(expected_packages), actual=sorted(actual_packages))
    for record in revisions:
        name = record['name']
        prefix = name + '/'
        expected = {rel[len(prefix):] for rel in baseline if rel.startswith(prefix)}
        if len(expected) != record['tracked_files']:
            failure('dependency_baseline_count', package=name, expected=record['tracked_files'], actual=len(expected))
        for label, base in [('original', ORIGINAL), ('reproduction', REPRO)]:
            root = local_path(base, '.lake/packages/' + name)
            try:
                actual = tracked_paths(root)
                added, missing = sorted(actual - expected), sorted(expected - actual)
                row = {'package': name, 'tree': label, 'expected_count': len(expected),
                       'actual_count': len(actual), 'added': added, 'missing': missing}
                if added or missing:
                    failure('dependency_tracked_set_changed', **row)
            except Exception as exc:
                row = {'package': name, 'tree': label, 'error': str(exc)}
                failure('dependency_tracked_set_unavailable', **row)
            rows.append(row)
    return rows


def normalize_newlines(text):
    return text.replace('\r\n', '\n')


def check_website():
    evidence = read_json(SITE / 'content/evidence.json')
    definitions = read_json(SITE / 'content/definitions.json')
    records = []

    def one(label, rel, start, end, literal, capture, expected_file_hash=None):
        try:
            path = local_path(REPRO, rel)
            text = normalize_newlines(path.read_bytes().decode('utf-8'))
            if not isinstance(start, int) or not isinstance(end, int) or start < 1 or end < start:
                raise ValueError('Invalid inclusive source line range')
            lines = text.splitlines(keepends=True)
            if end > len(lines):
                raise ValueError('Source line range exceeds file')
            if capture == 'complete-source-lines':
                expected = ''.join(lines[start-1:end])
            else:
                # This content format was originally produced by joining splitlines().
                # Remove only the final line separator of each selected line, never whitespace.
                expected = '\n'.join(line.removesuffix('\n') for line in lines[start-1:end])
            matches = normalize_newlines(literal) == expected
            file_hash = sha(path)
            hash_matches = expected_file_hash is None or file_hash == expected_file_hash.lower()
            record = {'name': label, 'file': rel, 'start': start, 'end': end, 'capture': capture,
                      'matches': matches, 'file_sha256': file_hash, 'file_hash_matches': hash_matches}
            if not matches or not hash_matches:
                failure('website_source_mismatch', **record)
        except Exception as exc:
            record = {'name': label, 'file': rel, 'error': str(exc), 'matches': False}
            failure('website_source_unavailable', **record)
        records.append(record)

    for family in ['endpoints', 'statements', 'predicates']:
        for item in evidence.get(family, []):
            one(family + ':' + item['symbol'], item['source_path'], item['line_start'], item['line_end'],
                item['literal'], 'joined-lines-no-final-separator', item.get('source_sha256'))
            for i, context in enumerate(item.get('implicit_context', [])):
                one(family + ':' + item['symbol'] + f':context:{i}', item['source_path'],
                    context['line_start'], context['line_end'], context['literal'], 'joined-lines-no-final-separator')
    for family in ['definitions', 'standardMathlib']:
        for item in definitions.get(family, []):
            for i, source in enumerate([item['source']] + item.get('sourceContext', [])):
                one(family + ':' + item['name'] + (f':context:{i-1}' if i else ''),
                    source['file'], source['startLine'], source['endLine'], source['snippet'], 'complete-source-lines')
    if len(evidence.get('endpoints', [])) != 5 or len(evidence.get('statements', [])) != 5:
        failure('website_endpoint_statement_count', endpoints=len(evidence.get('endpoints', [])),
                statements=len(evidence.get('statements', [])))
    if len(definitions.get('definitions', [])) != 20 or len(definitions.get('standardMathlib', [])) != 7:
        failure('website_definition_count', project=len(definitions.get('definitions', [])),
                mathlib=len(definitions.get('standardMathlib', [])))
    return {'comparison_policy': 'CRLF to LF only; no strip, space, indentation or code normalization. Each content format retains its recorded whole-line / joined-line extraction contract.',
            'snippets_and_contexts': len(records), 'records': records}


def load_lexer():
    copied = output('identity-preserved-placeholder-lexer.py')
    original = OLD_LEXER.read_bytes()
    if copied.exists() and copied.read_bytes() != original:
        raise ValueError('Existing evidence lexer copy differs from preserved helper')
    if not copied.exists():
        copied.write_bytes(original)
    old_bytecode = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec = importlib.util.spec_from_file_location('fresh_audit_preserved_lexer', copied)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = old_bytecode
    # The imported module's __name__ is not __main__; its old main/writers are never called.
    return module, {'copied_source': str(OLD_LEXER), 'copy': copied.name,
                    'sha256': hashlib.sha256(original).hexdigest(),
                    'self_test': module.scanner_self_test(), 'old_main_executed': False}


def lean_files(root):
    for current, dirs, files in os.walk(root, followlinks=False):
        current = Path(current)
        retained = []
        for name in dirs:
            if name in {'.lake', '.git', '.cache', 'node_modules', '__pycache__'}:
                continue
            path = current / name
            if is_reparse(path):
                failure('scan_reparse_directory', path=str(path))
            else:
                retained.append(name)
        dirs[:] = retained
        for name in files:
            path = current / name
            if path.suffix == '.lean':
                if is_reparse(path):
                    failure('scan_reparse_file', path=str(path))
                else:
                    yield path


def artifact_source_map(package_root, label):
    lib = local_path(package_root, '.lake/build/lib/lean')
    entries = []
    if not lib.is_dir():
        return entries
    for artifact in sorted(lib.rglob('*.olean')):
        if is_reparse(artifact):
            failure('artifact_reparse', path=str(artifact))
            continue
        relative = artifact.relative_to(lib).with_suffix('.lean').as_posix()
        source = local_path(package_root, relative)
        module = relative.removesuffix('.lean').replace('/', '.')
        row = {'package': label, 'module': module, 'source': str(source),
               'artifact': str(artifact), 'source_exists': source.is_file()}
        entries.append(row)
        if not row['source_exists']:
            failure('built_module_source_missing', **row)
    return entries


def supplementary_scan(lexer, revisions, project_manifest, dependency_manifest):
    project_paths = sorted(lean_files(REPRO))
    imports, by_module = {}, {}
    for path in project_paths:
        rel = path.relative_to(REPRO).as_posix()
        module = rel.removesuffix('.lean').replace('/', '.')
        clean, _, _, issues = lexer.lex(path.read_bytes().decode('utf-8-sig'))
        names, import_errors = lexer.imports_from(clean)
        imports[module] = names
        by_module[module] = path
        if issues or import_errors:
            failure('project_lex_or_import_errors', source=rel, lex=issues, imports=import_errors)
    if 'ComplementedSubspace' not in imports:
        raise ValueError('Integration root source is absent')
    closure, frontier, queue = set(), set(), deque(['ComplementedSubspace'])
    while queue:
        module = queue.popleft()
        if module in closure:
            continue
        closure.add(module)
        for imported in imports[module]:
            if imported in imports:
                queue.append(imported)
            else:
                frontier.add(imported)
    endpoints = {'ComplementedSubspace.RealMainTheorem', 'ComplementedSubspace.RealMainConsequences',
                 'ComplementedSubspace.ComplexCorollary'}
    if not endpoints <= closure:
        failure('root_endpoint_module_coverage', missing=sorted(endpoints - closure))

    project_artifacts = artifact_source_map(REPRO, 'project')
    built_local = {r['module'] for r in project_artifacts}
    if not closure <= built_local:
        failure('imported_project_modules_without_olean', modules=sorted(closure - built_local))
    external_artifacts = []
    for package in revisions:
        package_root = local_path(REPRO, '.lake/packages/' + package['name'])
        package_rows = artifact_source_map(package_root, package['name'])
        for row in package_rows:
            rel = package['name'] + '/' + Path(row['source']).relative_to(package_root).as_posix()
            row['in_dependency_tracked_manifest'] = rel in dependency_manifest
            if rel not in dependency_manifest:
                failure('built_external_source_outside_tracked_manifest', **row)
        external_artifacts.extend(package_rows)
    if not external_artifacts:
        failure('no_built_external_modules')

    work = []
    for module, path in by_module.items():
        rel = path.relative_to(REPRO).as_posix()
        scope = 'project-imported' if module in closure else 'project-unrelated-or-audit'
        if module in closure and rel not in project_manifest:
            failure('imported_project_source_not_in_manifest', file=rel)
        work.append((path, scope, module, 'project'))
    for path in sorted(lean_files(EVIDENCE)):
        work.append((path, 'fresh-evidence-audit-only', path.stem, 'audit'))
    for row in external_artifacts:
        if row['source_exists']:
            work.append((Path(row['source']), 'external-built-module-source', row['module'], row['package']))

    counts, token_counts, reviewed_external, gate_hits, file_rows = Counter(), Counter(), 0, [], []
    with output('lexical-occurrences.jsonl').open('w', encoding='utf-8') as stream:
        for path, scope, module, package in work:
            before = sha(path)
            text = path.read_bytes().decode('utf-8-sig')
            clean, kinds, constructs, issues = lexer.lex(text)
            if issues:
                failure('scan_lexical_incomplete', scope=scope, module=module, issues=issues)
            file_hits, active_hits = 0, 0
            for match in lexer.TOKEN_RE.finditer(text):
                token = match.group()
                kind = kinds[match.start()]
                line, column, source = lexer.line_info(text, match.start())
                # Quotes in Lean metaprograms remain conservatively classified as code.
                # Only the project-imported gate rejects listed executable token spellings.
                gate = scope == 'project-imported' and kind == 'code' and token in BLOCKED_PROJECT_TOKENS
                row = {'scope': scope, 'package': package, 'module': module, 'file': str(path),
                       'line': line, 'column': column, 'token': token, 'kind': kind,
                       'source': source, 'project_gate': gate}
                stream.write(json.dumps(row, ensure_ascii=False) + '\n')
                file_hits += 1
                active_hits += kind == 'code'
                counts[scope + ':' + kind] += 1
                token_counts[scope + ':' + kind + ':' + token] += 1
                if gate:
                    gate_hits.append(row)
                if scope == 'external-built-module-source' and kind == 'code':
                    reviewed_external += 1
            after = sha(path)
            if after != before:
                failure('source_changed_during_lexical_scan', file=str(path), before=before, after=after)
            file_rows.append({'file': str(path), 'scope': scope, 'package': package, 'module': module,
                              'sha256': after, 'bytes': path.stat().st_size, 'lines': len(text.splitlines()),
                              'hits': file_hits, 'executable_hits': active_hits, 'constructs': constructs})
    if gate_hits:
        failure('project_imported_placeholder_or_trust_override', occurrences=gate_hits)
    save('lexical-source-inventory.json', file_rows)
    save('built-module-source-map.json', project_artifacts + external_artifacts)
    return {'scope': 'All reproduction local Lean sources and fresh evidence audit Lean files; external package source selected by .olean artifacts under each isolated .lake/build/lib/lean.',
            'built_artifact_caveat': 'Artifact presence selects supplementary scan scope only; it is not proof of successful fresh compilation or kernel replay.',
            'external_caveat': 'External unsafe/meta/native/axiom/placeholder-related token hits require review. Such spellings can belong to quotations, metaprogram implementations, tests or sound proof-producing machinery; they are not automatically mathematical assumptions.',
            'core_caveat': 'Pinned toolchain Lean/Init/Lake sources are not selected by package build directories and are outside this supplementary scan.',
            'lexer_caveat': 'Conservative source-text lexer, not a Lean parser; syntax quotations remain code. Project gate rejects any executable spelling in its listed token set, including a trust setting that would need semantic review to establish harmlessness.',
            'project_gate_tokens': sorted(BLOCKED_PROJECT_TOKENS),
            'project_import_closure': sorted(closure), 'external_import_frontier': sorted(frontier),
            'files_by_scope': dict(Counter(r['scope'] for r in file_rows)),
            'project_built_modules': len(project_artifacts), 'external_built_modules': len(external_artifacts),
            'external_packages_with_artifacts': dict(Counter(r['package'] for r in external_artifacts)),
            'all_occurrence_counts': dict(counts), 'token_counts': dict(token_counts),
            'project_gate_hits': len(gate_hits), 'external_executable_hits_for_review': reviewed_external,
            'occurrence_details': 'identity-lexical-occurrences.jsonl',
            'inventory': 'identity-lexical-source-inventory.json'}


def main():
    REPORT['started_utc'] = now()
    if not EVIDENCE.is_dir() or is_reparse(EVIDENCE) or is_reparse(AUDIT):
        raise ValueError('The fixed fresh evidence directory must already exist without reparse points')
    if output('source-and-scan.json').exists():
        raise ValueError('Refusing to overwrite a prior identity-source-and-scan.json result')
    if ORIGINAL.resolve() == REPRO.resolve():
        raise ValueError('Original and reproduction paths coincide')
    original_before = read_manifest('source-manifest-before.sha256')
    reproduced_before = read_manifest('reproduction-source-manifest-before.sha256')
    dependency_before = read_manifest('dependency-source-manifest-before.sha256')
    if original_before != reproduced_before:
        failure('original_reproduction_baseline_difference')
    snapshot = read_json(EVIDENCE / 'snapshot.json')
    if snapshot.get('source_file_count') != EXPECTED_PROJECT_COUNT:
        failure('snapshot_count', actual=snapshot.get('source_file_count'))
    if snapshot.get('source_manifest_sha256') != sha(EVIDENCE / 'source-manifest-before.sha256'):
        failure('baseline_manifest_hash_changed')
    site_preserved = {x['path'].replace('\\', '/'): x['after_sha256'] for x in
                      read_json(SITE / 'public/companion-source-recheck.json')['comparison']['files']}
    if site_preserved != original_before:
        failure('website_preserved_manifest_differs_from_original_baseline')
    revisions = read_json(EVIDENCE / 'dependency-revisions.json')
    manifest_results = []
    for label, root, baseline, count in [
        ('original-source', ORIGINAL, original_before, EXPECTED_PROJECT_COUNT),
        ('reproduction-source', REPRO, reproduced_before, EXPECTED_PROJECT_COUNT),
        ('original-dependency-source', ORIGINAL / '.lake/packages', dependency_before, None),
        ('reproduction-dependency-source', REPRO / '.lake/packages', dependency_before, None),
    ]:
        result, _ = check_manifest(label, root, baseline, count)
        manifest_results.append(result)
    REPORT['manifests'] = manifest_results
    REPORT['dependency_tracked_sets'] = check_dependency_tracked_sets(dependency_before, revisions)
    REPORT['website_identity'] = check_website()
    lexer, REPORT['preserved_lexer'] = load_lexer()
    REPORT['supplementary_scan'] = supplementary_scan(lexer, revisions, reproduced_before, dependency_before)
    # Recheck at completion: comparisons above must not conceal source changes during the scan.
    final_stability = []
    for label, root, baseline in [
        ('original-source-final', ORIGINAL, original_before),
        ('reproduction-source-final', REPRO, reproduced_before),
        ('original-dependency-source-final', ORIGINAL / '.lake/packages', dependency_before),
        ('reproduction-dependency-source-final', REPRO / '.lake/packages', dependency_before),
    ]:
        result, _ = check_manifest(label, root, baseline)
        final_stability.append(result)
    REPORT['end_of_scan_manifest_stability'] = final_stability


def finish():
    REPORT['ended_utc'] = now()
    REPORT['pass'] = not REPORT['failures']
    REPORT['status'] = 'PASS: identity and supplementary project gate only' if REPORT['pass'] else 'FAILED CHECK'
    REPORT['not_certified_by_this_helper'] = [
        'fresh build completion', 'kernel replay', 'endpoint proof types/axiom allowlist',
        'external metaprogram trust review', 'mathematical correspondence with the manuscript',
    ]
    save('source-and-scan.json', REPORT)
    scan = REPORT.get('supplementary_scan', {})
    text = '\n'.join([
        'SOURCE IDENTITY AND SUPPLEMENTARY LEXICAL AUDIT', REPORT['status'],
        f'Start: {REPORT["started_utc"]}', f'End: {REPORT["ended_utc"]}',
        f'Original: {ORIGINAL}', f'Reproduction: {REPRO}',
        f'Expected project manifest files per tree: {EXPECTED_PROJECT_COUNT}',
        'Manifest results: ' + json.dumps(REPORT.get('manifests', [])),
        'Files scanned by scope: ' + json.dumps(scan.get('files_by_scope', {})),
        'Project imported gate hits: ' + str(scan.get('project_gate_hits', 'NOT COMPLETED')),
        'External executable hits requiring review: ' + str(scan.get('external_executable_hits_for_review', 'NOT COMPLETED')),
        'Website snippets/contexts checked: ' + str(REPORT.get('website_identity', {}).get('snippets_and_contexts', 'NOT COMPLETED')),
        'Failure count: ' + str(len(REPORT['failures'])),
        'This report is supplementary; it does not establish successful build, kernel replay, or external metaprogram trust.',
        'Full details: identity-source-and-scan.json; identity-lexical-occurrences.jsonl; identity-lexical-source-inventory.json',
    ]) + '\n'
    output('source-and-scan.txt').write_text(text, encoding='utf-8')
    print(text, end='')
    return 0 if REPORT['pass'] else 2


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    try:
        main()
    except Exception as exc:
        failure('helper_exception', error=str(exc), traceback=traceback.format_exc())
    # Avoid overwriting previous results after the explicit pre-existing-result refusal.
    if EVIDENCE.is_dir() and not (EVIDENCE / 'identity-source-and-scan.json').exists():
        sys.exit(finish())
    print(json.dumps(REPORT, ensure_ascii=False, indent=2), file=sys.stderr)
    sys.exit(2)
