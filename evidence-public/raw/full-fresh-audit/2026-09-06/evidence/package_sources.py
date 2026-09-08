"""Package pinned tracked source bytes only; no compiler outputs or Git metadata."""
from audit_runner import *

def main():
    output = ROOT / 'source'
    output.mkdir(exist_ok=True)
    target = output / 'dependency-sources.zip'
    if target.exists():
        raise RuntimeError('Refusing to overwrite an existing source package')
    manifest = (EVIDENCE / 'dependency-source-manifest-before.sha256').read_text().splitlines()
    records = []
    with zipfile.ZipFile(target, 'x', zipfile.ZIP_DEFLATED, compresslevel=6) as archive:
        for row in manifest:
            digest, relative = row.split('  ', 1)
            path = REPRO / '.lake/packages' / relative
            if not path.resolve().is_relative_to((REPRO / '.lake/packages').resolve()):
                raise RuntimeError('Source archive path escaped reproduction')
            data = path.read_bytes()
            if hashlib.sha256(data).hexdigest() != digest:
                raise RuntimeError('Source differs from pinned manifest: ' + relative)
            archive.writestr(relative, data)
            records.append((relative, digest))
        archive.writestr('CONTENTS.sha256', ''.join(f'{h}  {p}\n' for p,h in records))
    with zipfile.ZipFile(target) as archive:
        if archive.testzip() is not None:
            raise RuntimeError('Source archive CRC failure')
        if set(archive.namelist()) != {p for p,h in records} | {'CONTENTS.sha256'}:
            raise RuntimeError('Source archive member-set mismatch')
        for relative, digest in records:
            if hashlib.sha256(archive.read(relative)).hexdigest() != digest:
                raise RuntimeError('Source archive digest failure: ' + relative)
    frozen = ROOT / 'checkpoint/frozen-project-source.zip'
    destination = output / frozen.name
    if destination.exists():
        raise RuntimeError('Refusing to overwrite frozen source archive')
    destination.write_bytes(frozen.read_bytes())
    save('source-archive-validation.json', {
        'completed': now(), 'status': 'PASS',
        'dependency_source_count': len(records),
        'dependency_source_archive': str(target),
        'dependency_source_archive_bytes': target.stat().st_size,
        'dependency_source_archive_sha256': sha(target),
        'all_dependency_members_crc_and_sha256_checked': True,
        'project_source_archive_sha256': sha(destination),
        'project_archive_matches_checkpoint': sha(destination) == sha(frozen),
        'contents': 'Pinned tracked source files, including tracked ProofWidgets JS inputs; no Git metadata or precompiled Lean artifacts.',
    })
    print((EVIDENCE / 'source-archive-validation.json').read_text())

if __name__ == '__main__':
    main()
