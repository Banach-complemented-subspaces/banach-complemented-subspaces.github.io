from pathlib import Path
import hashlib,json,zipfile
root=Path('output/full_fresh_audit_2026-09-06_102854')
e=root/'evidence'
site=Path('output/complemented-subspace-companion')
with zipfile.ZipFile(root/'checkpoint/website-qa.zip','w',zipfile.ZIP_DEFLATED) as z:
    for p in (site/'qa').rglob('*'):
        if p.is_file(): z.write(p,p.relative_to(site))
checkpoint=json.loads((e/'checkpoint.json').read_text())
p=root/'checkpoint/website-qa.zip'
checkpoint[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
(e/'checkpoint.json').write_text(json.dumps(checkpoint,indent=2),encoding='utf-8')
tool=Path('tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows')
files=list((tool/'bin').glob('*lean*.dll'))+list((tool/'lib/lean').glob('*.dll'))
rows=[{'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]
(e/'retained-kernel-library-hashes.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')
for rel in ['src/lean/LeanChecker.lean','src/lean/Lean/Replay.lean']:
    p=tool/rel
    (e/('pinned-'+p.name)).write_bytes(p.read_bytes())
print('Saved website QA checkpoint and retained kernel-library identities.')
