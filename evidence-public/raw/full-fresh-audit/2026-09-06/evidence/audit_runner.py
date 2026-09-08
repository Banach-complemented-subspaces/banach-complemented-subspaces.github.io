"""Audit-only bounded runner. Never modifies mathematical source or the checker."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys, time, zipfile

EVIDENCE = Path(__file__).resolve().parent
ROOT = EVIDENCE.parent
WORKSPACE = ROOT.parent.parent
PROJECT = WORKSPACE / 'output/lean_trial_2026-09-05'
SITE = WORKSPACE / 'output/complemented-subspace-companion'
TOOLCHAIN = WORKSPACE / 'tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows'
BIN = TOOLCHAIN / 'bin'
REPRO = ROOT / 'reproduction'
GIT = Path('C:/Program Files/Git/cmd/git.exe')
DEADLINE = datetime.datetime.fromisoformat('2026-09-06T13:13:54+00:00').timestamp()
EVIDENCE.mkdir(parents=True, exist_ok=True)

def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''): h.update(chunk)
    return h.hexdigest()
def save(name, value):
    (EVIDENCE / name).write_text(json.dumps(value, indent=2, ensure_ascii=False), encoding='utf-8')
def env_base():
    env = os.environ.copy()
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME', 'LAKE_PACKAGES_DIR']:
        env.pop(key, None)
    env['PATH'] = str(BIN) + os.pathsep + env.get('PATH', '')
    env['PYTHONIOENCODING'] = 'utf-8'
    return env
def run(label, args, cwd=PROJECT, env=None, timeout=None):
    if (EVIDENCE / (label + '.command.json')).exists():
        raise RuntimeError('Refusing to overwrite recorded command: ' + label)
    args = list(map(str, args)); env = env or env_base()
    budget = DEADLINE - time.time()
    if timeout is not None: budget = min(timeout, budget)
    if budget <= 0: raise TimeoutError('Audit computation deadline reached; reserve time for evidence')
    record = dict(label=label, cwd=str(cwd), executable=args[0], arguments=args[1:],
                  windows_command_line=subprocess.list2cmdline(args), started=now(),
                  environment={k:v for k,v in env.items() if k.startswith(('LEAN','LAKE','MATHLIB')) or k in ['PATH','PYTHONIOENCODING']},
                  stdout=label+'.stdout.log', stderr=label+'.stderr.log', timeout_seconds=budget)
    save(label + '.command.json', record)
    start = time.monotonic()
    with (EVIDENCE / record['stdout']).open('wb') as out, (EVIDENCE / record['stderr']).open('wb') as err:
        try:
            process = subprocess.Popen(args, cwd=cwd, env=env, stdout=out, stderr=err,
                                       creationflags=subprocess.CREATE_NO_WINDOW | subprocess.CREATE_NEW_PROCESS_GROUP)
            record['pid'] = process.pid; save(label + '.command.json', record)
            try:
                code = process.wait(timeout=budget)
                record.update(exit_code=code, timed_out=False,
                              status='PASS' if code == 0 else 'FAILED CHECK')
            except subprocess.TimeoutExpired:
                # Terminate only this runner-owned process tree; never other Lean/Codex processes.
                kill = subprocess.run(['C:/Windows/System32/taskkill.exe', '/PID', str(process.pid), '/T', '/F'], capture_output=True)
                (EVIDENCE / (label+'.timeout-stop.log')).write_bytes(kill.stdout + kill.stderr)
                record.update(exit_code=process.wait(), timed_out=True, status='NOT COMPLETED', stop_exit_code=kill.returncode)
        except OSError as e:
            record.update(exit_code=None, timed_out=False, status='NOT COMPLETED', launch_error=str(e))
    record.update(ended=now(), elapsed_seconds=time.monotonic()-start)
    save(label + '.command.json', record)
    with (EVIDENCE / (label+'.log')).open('wb') as log:
        log.write((json.dumps(record, ensure_ascii=False, indent=2)+'\n\nSTDOUT (verbatim)\n').encode())
        log.write((EVIDENCE / record['stdout']).read_bytes())
        log.write(b'\nSTDERR (verbatim)\n'); log.write((EVIDENCE / record['stderr']).read_bytes())
    print(json.dumps({k:record.get(k) for k in ['label','status','exit_code','elapsed_seconds']}), flush=True)
    return record

def project_files():
    comparison = json.loads((SITE/'public/companion-source-recheck.json').read_text())['comparison']
    return [(row['path'], row['after_sha256']) for row in comparison['files']]
def manifest(name, root, files):
    entries = [(p.replace('\\','/'), sha(root/p)) for p in files]
    (EVIDENCE/name).write_text(''.join(f'{h}  {p}\n' for p,h in entries), encoding='utf-8')
    return dict(entries)

def initial():
    save('status.json', {'started':'2026-09-06T10:28:54+00:00', 'overall':'RUNNING',
        'computation_deadline':'2026-09-06T13:13:54+00:00', 'handoff_deadline':'2026-09-06T13:28:54+00:00',
        'target':'ComplementedSubspace', 'stages':{}})
    files = project_files()
    before = manifest('source-manifest-before.sha256', PROJECT, [p for p,h in files])
    if any(before[p.replace('\\','/')] != h for p,h in files): raise RuntimeError('Frozen source differs from prior approved snapshot')
    save('snapshot.json', {'source_manifest_sha256':sha(EVIDENCE/'source-manifest-before.sha256'),
        'source_file_count':len(files),'project':str(PROJECT),'toolchain':str(TOOLCHAIN),
        'initial_root_artifact':str(PROJECT/'.lake/build/lib/lean/ComplementedSubspace.olean'),
        'initial_root_artifact_sha256':sha(PROJECT/'.lake/build/lib/lean/ComplementedSubspace.olean'),
        'root_imports':(PROJECT/'ComplementedSubspace.lean').read_text(),
        'toolchain_executables':{n:sha(BIN/n) for n in ['lean.exe','lake.exe','leanchecker.exe']}})
    checkpoint = ROOT/'checkpoint'; checkpoint.mkdir(exist_ok=True)
    for label, folder, exclude in [
        ('website',SITE,{'node_modules','.git','qa'}),
        ('previous-audit',PROJECT/'verification/independent-audit-2026-09-05',set())]:
        with zipfile.ZipFile(checkpoint/(label+'.zip'),'w',zipfile.ZIP_DEFLATED) as z:
            for parent, dirs, names in os.walk(folder):
                dirs[:] = [d for d in dirs if d not in exclude]
                for name in names:
                    p=Path(parent)/name; z.write(p, p.relative_to(folder))
    with zipfile.ZipFile(checkpoint/'frozen-project-source.zip','w',zipfile.ZIP_DEFLATED) as z:
        for p,h in files: z.write(PROJECT/p,p)
        for name in ['README.md','BUILDING.md']: z.write(PROJECT/name,name)
    save('checkpoint.json', {p.name:sha(p) for p in checkpoint.glob('*.zip')})
    for label,args in [('lean-version',[BIN/'lean.exe','--version']),('lake-version',[BIN/'lake.exe','--version']),
            ('project-git-head',[GIT,'rev-parse','HEAD']),('project-git-status',[GIT,'status','--short','--untracked-files=normal']),
            ('original-search-path',[BIN/'lake.exe','env',sys.executable,'-c','import os; print("\\n".join(k+"="+v for k,v in os.environ.items() if k.startswith(("LEAN","LAKE","MATHLIB"))))'])]:
        run(label,args,timeout=120)
    (EVIDENCE/'environment.txt').write_text('Pinned retained toolchain: '+str(TOOLCHAIN)+'\nlean-toolchain:\n'+(PROJECT/'lean-toolchain').read_text()+'\nExecutable identity: snapshot.json\nNative command outputs: lean-version.log, lake-version.log, original-search-path.log, project-git-head.log, project-git-status.log\nInitial Lake PID 7848 seen during discovery had exited before the read-only process query; no process was stopped. No overlapping Lean build was present.\n',encoding='utf-8')
    record=run('initial-fresh-replay',[BIN/'lake.exe','env',BIN/'leanchecker.exe','--fresh','--verbose','ComplementedSubspace'],timeout=3600)
    state=json.loads((EVIDENCE/'status.json').read_text()); state['stages']['2_existing_fresh_replay']=record['status']; save('status.json',state)

if __name__=='__main__':
    try: initial()
    except Exception as e:
        import traceback
        (EVIDENCE/'initial-runner-error.txt').write_text(traceback.format_exc(),encoding='utf-8')
        raise
