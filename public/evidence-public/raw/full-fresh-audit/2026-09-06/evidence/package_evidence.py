"""Final evidence packaging, with an internal manifest and detached validation receipt.

Requires all reviewed checks to pass. Final PASS documents are published to disk
only after the archive containing their exact bytes has passed CRC and SHA checks.
"""
from audit_runner import *
from render_report import render

def main():
    state = json.loads((EVIDENCE/'status.json').read_text(encoding='utf-8'))
    prerequisites = [
        '1_source_environment_target_identity', '2_existing_fresh_replay',
        '3_source_reproduction', '4_rebuilt_fresh_replay',
        '5_endpoint_definition_axiom_checks',
    ]
    if any(state['stages'].get(stage) != 'PASS' for stage in prerequisites):
        raise RuntimeError('Cannot package an overall PASS with an incomplete prerequisite')
    for filename in ['final-preservation.json', 'source-archive-validation.json']:
        if json.loads((EVIDENCE/filename).read_text(encoding='utf-8'))['status'] != 'PASS':
            raise RuntimeError('Packaging prerequisite rejected: '+filename)
    for label in ['initial-fresh-replay', 'source-rebuild', 'rebuilt-fresh-replay',
                  'endpoint-types-and-axioms', 'printed-mathematical-definitions',
                  'review-formulation-identity', 'source-identity-and-placeholder-scan',
                  'resolved-build-input-check', 'final-preservation-check']:
        command=json.loads((EVIDENCE/(label+'.command.json')).read_text(encoding='utf-8'))
        if command.get('exit_code') != 0 or command.get('timed_out') or not command.get('ended'):
            raise RuntimeError('Required native command did not complete successfully: '+label)
    destination=ROOT/'full-fresh-audit-evidence.zip'
    pending=ROOT/'full-fresh-audit-evidence.pending.zip'
    receipt_path=ROOT/'archive-validation.json'
    if any(p.exists() for p in [destination,pending,receipt_path]):
        raise RuntimeError('Refusing to replace an existing evidence archive or receipt')
    state['stages']['6_final_preservation_and_packaging']='PASS'
    state['overall']='PASS'
    state['label']='FULL FRESH AUDIT: PASS'
    state['report_assembled_utc']=now()
    state['archive_validation_receipt']='../archive-validation.json'
    state['source_manifest_sha256']=sha(EVIDENCE/'source-manifest-before.sha256')
    overrides={'evidence/status.json':json.dumps(state,indent=2,ensure_ascii=False).encode('utf-8')}
    for filename in ['report.md','FINAL_FRESH_AUDIT_STATUS.md']:
        draft=EVIDENCE/(filename+'.draft')
        data=draft.read_text(encoding='utf-8')
        if data.count('PACKAGING_PENDING') != 1:
            raise RuntimeError('Expected exactly one packaging status marker in '+str(draft))
        overrides['evidence/'+filename]=data.replace('PACKAGING_PENDING','PASS').encode('utf-8')
    overrides['evidence/report.html']=render(overrides['evidence/report.md'].decode('utf-8')).encode('utf-8')
    records={}
    started=now()
    with zipfile.ZipFile(pending,'x',zipfile.ZIP_DEFLATED,compresslevel=6) as archive:
        for directory in [EVIDENCE,ROOT/'source']:
            for file in sorted(directory.rglob('*')):
                if not file.is_file() or '__pycache__' in file.parts or file.suffix in {'.pyc','.draft'}:
                    continue
                # The packaging command and its detached receipt finish after this archive.
                if file.name.startswith('evidence-packaging'):
                    continue
                relative=file.relative_to(ROOT).as_posix()
                if relative in overrides:
                    continue
                if file.is_symlink() or not file.resolve().is_relative_to(ROOT.resolve()):
                    raise RuntimeError('Evidence path escaped the declared audit directory')
                records[relative]=sha(file)
                archive.write(file,relative)
        for relative,data in overrides.items():
            archive.writestr(relative,data)
            records[relative]=hashlib.sha256(data).hexdigest()
        manifest=''.join(f'{records[name]}  {name}\n' for name in sorted(records)).encode('utf-8')
        archive.writestr('CONTENTS.sha256',manifest)
    with zipfile.ZipFile(pending) as archive:
        if len(archive.namelist()) != len(set(archive.namelist())):
            raise RuntimeError('Archive contains duplicate member names')
        if set(archive.namelist()) != set(records)|{'CONTENTS.sha256'}:
            raise RuntimeError('Archive member set differs from manifest')
        if archive.read('CONTENTS.sha256') != manifest:
            raise RuntimeError('Archive manifest differs from generated exact bytes')
        bad_crc=archive.testzip()
        if bad_crc is not None:
            raise RuntimeError('Archive CRC rejected '+bad_crc)
        for name,expected in records.items():
            h=hashlib.sha256()
            with archive.open(name) as source:
                for chunk in iter(lambda:source.read(1024*1024),b''):
                    h.update(chunk)
            if h.hexdigest()!=expected:
                raise RuntimeError('Archive SHA-256 rejected '+name)
    # This is a rename of one newly generated file inside the checked audit root.
    pending.rename(destination)
    for relative,data in overrides.items():
        (ROOT/relative).write_bytes(data)
    (ROOT/'FINAL_FRESH_AUDIT_STATUS.md').write_bytes(overrides['evidence/FINAL_FRESH_AUDIT_STATUS.md'])
    receipt=dict(status='PASS',started=started,completed=now(),archive=destination.name,
        archive_bytes=destination.stat().st_size,archive_sha256=sha(destination),
        checked_content_files=len(records),internal_manifest='CONTENTS.sha256',
        internal_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
        exact_member_set_checked=True,all_members_crc_checked=True,all_members_sha256_checked=True,
        full_audit_elapsed_seconds=time.time()-datetime.datetime.fromisoformat(state['started']).timestamp(),
        exclusion_note='The manifest excludes itself. This detached receipt and the final packaging process record are outside the archive to avoid self-reference; all Lean run records and raw streams are included.',
        privacy_note='Unredacted local evidence includes Windows personal paths and username. Review/redact a separately labelled copy before public release. No project material was uploaded or published.')
    receipt_path.write_text(json.dumps(receipt,indent=2),encoding='utf-8')
    (ROOT/'full-fresh-audit-evidence.zip.sha256').write_text(receipt['archive_sha256']+'  '+destination.name+'\n',encoding='utf-8')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':
    main()
