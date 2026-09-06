"""Final read-only preservation checks after the expensive Lean runs."""
from audit_runner import *

def compare_archive(archive_path, original_root):
    mismatches = []
    count = 0
    with zipfile.ZipFile(archive_path) as archive:
        if archive.testzip() is not None:
            raise RuntimeError('Checkpoint CRC check rejected ' + str(archive_path))
        for member in archive.infolist():
            if member.is_dir():
                continue
            count += 1
            file = original_root / member.filename
            expected = hashlib.sha256(archive.read(member)).hexdigest()
            actual = sha(file) if file.is_file() else None
            if expected != actual:
                mismatches.append(dict(path=str(file), expected=expected, actual=actual))
    return dict(archive=str(archive_path), original_root=str(original_root), files=count,
                mismatches=mismatches, status='PASS' if not mismatches else 'FAILED CHECK')

def main():
    if (EVIDENCE/'final-preservation.json').exists():
        raise RuntimeError('Refusing to overwrite final preservation evidence')
    started = now()
    results = []
    final_source_checks=[]
    for label,base,manifest_name in [
        ('original-project',PROJECT,'source-manifest-before.sha256'),
        ('reproduced-project',REPRO,'source-manifest-before.sha256'),
        ('original-dependencies',PROJECT/'.lake/packages','dependency-source-manifest-before.sha256'),
        ('reproduced-dependencies',REPRO/'.lake/packages','dependency-source-manifest-before.sha256'),
    ]:
        expected=dict((line.split('  ',1)[1],line.split('  ',1)[0]) for line in
            (EVIDENCE/manifest_name).read_text().splitlines() if line)
        actual=manifest('final-'+label+'.sha256',base,list(expected))
        bad=[p for p,h in expected.items() if actual.get(p)!=h]
        final_source_checks.append(dict(tree=label,files=len(expected),status='PASS' if not bad else 'FAILED CHECK',mismatches=bad))
    checkpoints = json.loads((EVIDENCE/'checkpoint.json').read_text())
    for name, expected in checkpoints.items():
        file = ROOT/'checkpoint'/name
        results.append(dict(path=str(file), expected=expected, actual=sha(file)))
    snapshot = json.loads((EVIDENCE/'snapshot.json').read_text())
    for name, expected in snapshot['toolchain_executables'].items():
        results.append(dict(path=str(BIN/name), expected=expected, actual=sha(BIN/name)))
    for entry in json.loads((EVIDENCE/'retained-kernel-library-hashes.json').read_text()):
        results.append(dict(path=entry['path'], expected=entry['sha256'], actual=sha(entry['path'])))
    artifact = Path(snapshot['initial_root_artifact'])
    results.append(dict(path=str(artifact), expected=snapshot['initial_root_artifact_sha256'], actual=sha(artifact)))
    for rel in ['src/lean/LeanChecker.lean','src/lean/Lean/Replay.lean']:
        file = TOOLCHAIN/rel
        results.append(dict(path=str(file), expected=sha(EVIDENCE/('pinned-'+file.name)), actual=sha(file)))
    for original, copy in [('BanLat/LICENSE','BanLat-LICENSE'), ('BanLat/PORTING.md','BanLat-PORTING.md')]:
        results.append(dict(path=str(PROJECT/original), expected=sha(EVIDENCE/copy), actual=sha(PROJECT/original)))
    archives = [compare_archive(ROOT/'checkpoint/previous-audit.zip', PROJECT/'verification/independent-audit-2026-09-05'),
                compare_archive(ROOT/'checkpoint/frozen-project-source.zip', PROJECT)]
    identity = json.loads((EVIDENCE/'identity-source-and-scan.json').read_text())
    identity_ok = identity['pass'] and all(r['matches'] for r in identity['end_of_scan_manifest_stability'])
    good = identity_ok and all(r['expected']==r['actual'] for r in results) and all(r['status']=='PASS' for r in archives) and all(r['status']=='PASS' for r in final_source_checks)
    save('final-preservation.json', dict(started=started, ended=now(), status='PASS' if good else 'FAILED CHECK',
        hashed_files=results, archive_comparisons=archives, final_source_manifest_identity=identity_ok, fresh_end_of_run_source_hashes=final_source_checks,
        identity_evidence='identity-source-and-scan.json',
        site_checkpoint='checkpoint/website.zip and checkpoint/website-qa.zip retain the complete earlier local site and QA before its authorized supplementary entry.'))
    after=EVIDENCE/'final-original-project.sha256'
    (EVIDENCE/'source-manifest-after.sha256').write_bytes(after.read_bytes())
    print(json.dumps({'status':'PASS' if good else 'FAILED CHECK', 'individual_files':len(results),
        'archive_files_compared':sum(a['files'] for a in archives), 'source_manifests_unchanged':identity_ok}))
    if not good:
        raise SystemExit(2)

if __name__=='__main__':
    main()
