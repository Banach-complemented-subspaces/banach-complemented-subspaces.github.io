"""Check public copies, archive members and privacy, without rerunning Lean."""
from pathlib import Path
import hashlib,io,json,re,zipfile

ROOT=Path(__file__).resolve().parents[1]
PUBLIC=ROOT/'public'
sha=lambda b:hashlib.sha256(b).hexdigest()
privacy=re.compile(rb'(?i)[a-z]:(?:[\\/]|%2f|%5c)+(?:Users|Documents(?:%20| )and(?:%20| )Settings)(?:[\\/]|%2f|%5c)+')
errors=[]
counts={'files':0,'archives':0,'archive_members':0}
def check(condition,message):
    if not condition: errors.append(message)
def scan(b,label):
    if zipfile.is_zipfile(io.BytesIO(b)):
        counts['archives']+=1
        with zipfile.ZipFile(io.BytesIO(b)) as z:
            check(z.testzip() is None,'ZIP CRC: '+label)
            for member in z.infolist():
                counts['archive_members']+=1
                check(not privacy.search(member.filename.encode()),'Personal archive member path: '+label)
                scan(z.read(member),label+'!'+member.filename)
            if 'PUBLIC_COPY_SHA256.json' in z.namelist():
                for m in json.loads(z.read('PUBLIC_COPY_SHA256.json')):
                    check(sha(z.read(m['path']))==m['public_sha256'],'Member hash: '+label+'!'+m['path'])
    else:
        check(not privacy.search(b),'Personal home path: '+label)
        # Upstream dependency configuration includes JSON-with-comments files.
        if label.endswith('.json') and '!source/dependency-sources.zip!' not in label:
            try: json.loads(b)
            except (ValueError,UnicodeError): errors.append('Invalid JSON: '+label)

manifest=json.loads((ROOT/'PUBLIC_FILES_SHA256.json').read_text(encoding='utf-8'))
expected={m['path'] for m in manifest}
actual={p.relative_to(PUBLIC).as_posix() for p in PUBLIC.rglob('*') if p.is_file()}
check(expected==actual,'Public manifest does not cover the exact public file set')
for m in manifest:
    p=PUBLIC/m['path']; b=p.read_bytes(); counts['files']+=1
    check(sha(b)==m['sha256'] and len(b)==m['bytes'],'Public hash/size: '+m['path'])
    scan(b,m['path'])
for m in json.loads((PUBLIC/'evidence-public/PUBLIC_COPY_SHA256.json').read_text()):
    b=(PUBLIC/m['public_path']).read_bytes()
    check(sha(b)==m['public_sha256'] and len(b)==m['public_bytes'],'Public-copy manifest: '+m['public_path'])
for folder in ['content','app','components','lean','paper']:
    for p in (ROOT/folder).rglob('*'):
        if p.is_file():
            check(not privacy.search(p.read_bytes()),'Personal home path in repository: '+p.relative_to(ROOT).as_posix())
preservation=json.loads((PUBLIC/'evidence-public/companion-source-recheck.json').read_text())['comparison']['files']
for m in preservation:
    check(sha((ROOT/'lean'/m['path']).read_bytes())==m['after_sha256'],'Frozen Lean source: '+m['path'])
result={'pass':not errors,**counts,'frozen_sources_checked':len(preservation),'errors':errors}
print(json.dumps(result,indent=2))
raise SystemExit(0 if not errors else 1)
