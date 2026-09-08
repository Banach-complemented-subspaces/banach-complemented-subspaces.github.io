"""Sequential source build, fresh replay and endpoint checks. Run only after initial replay."""
from audit_runner import *
from collections import Counter

def clean_env():
    env=env_base()
    env.update(LAKE_ARTIFACT_CACHE='false', LAKE_RESTORE_ARTIFACTS='false',
               LAKE_CACHE_DIR=str(ROOT/'isolated-lake-cache'),
               MATHLIB_NO_CACHE_ON_UPDATE='1', LEAN_NUM_THREADS='4')
    return env

def mark(stage,status):
    state=json.loads((EVIDENCE/'status.json').read_text())
    state['stages'][stage]=status; save('status.json',state)

def record_artifacts():
    result=[]
    packages=[('project',REPRO)]+[(p.name,p) for p in (REPRO/'.lake/packages').iterdir() if p.is_dir()]
    for package,folder in packages:
        lib=folder/'.lake/build/lib/lean'
        if not lib.exists(): continue
        for file in lib.rglob('*.olean'):
            rel=file.relative_to(lib)
            result.append(dict(package=package,module='.'.join(rel.with_suffix('').parts),
                path=str(file),sha256=sha(file),modified_utc=datetime.datetime.fromtimestamp(file.stat().st_mtime,datetime.timezone.utc).isoformat(),
                source=str(folder/rel.with_suffix('.lean'))))
    save('rebuilt-artifact-inventory.json',result)
    save('coverage.json',{'kind':'Inventory of actual isolated primary .olean outputs; not aggregate Lake jobs or replay-emitted counts',
        'by_package':dict(Counter(x['package'] for x in result)), 'primary_olean_count':len(result),
        'toolchain':'Retained pinned toolchain artifacts; safe imported logical declarations included by official fresh replay',
        'root_present':any(x['module']=='ComplementedSubspace' and x['package']=='project' for x in result)})
    (EVIDENCE/'coverage.txt').write_text((EVIDENCE/'coverage.json').read_text(),encoding='utf-8')

def main():
    initial=json.loads((EVIDENCE/'initial-fresh-replay.command.json').read_text())
    if 'ended' not in initial: raise RuntimeError('Initial replay still running; no second expensive run permitted')
    if not (EVIDENCE/'clean-state.json').exists(): raise RuntimeError('Independent source clean-state evidence missing')
    env=clean_env()
    for forbidden in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:
        if forbidden in env: raise RuntimeError('Inherited module path escaped cleanup')
    cache=ROOT/'isolated-lake-cache'
    if cache.exists() and any(cache.iterdir()): raise RuntimeError('Reproduction cache must initially be empty')
    cache.mkdir(exist_ok=True)
    # This check reads Lake's resolved path environment; it does not fetch module artifacts.
    paths=run('rebuilt-search-path-before',[BIN/'lake.exe','--no-cache','env',sys.executable,'-c',
      'import os; print("\\n".join(k+"="+v for k,v in os.environ.items() if k.startswith(("LEAN","LAKE","MATHLIB"))))'],REPRO,env,timeout=240)
    if paths['exit_code']!=0: mark('3_source_reproduction','NOT COMPLETED'); return
    path_text=(EVIDENCE/paths['stdout']).read_text()
    if str(PROJECT) in path_text: raise RuntimeError('Original project appears in isolated module search path')
    save('cache-controls.json',{'env':{k:v for k,v in env.items() if k.startswith(('LEAN','LAKE','MATHLIB'))},
        'lake_no_cache':True,'dependency_sources_clean':True,'no_mathlib_cache_download':True,
        'prebuild_module_paths':path_text,'mathematical_config_changes':False})
    mark('3_source_reproduction','RUNNING')
    build=run('source-rebuild',[BIN/'lake.exe','--no-cache','build','+ComplementedSubspace:olean'],REPRO,env)
    record_artifacts()
    mark('3_source_reproduction',build['status'])
    if build['exit_code']!=0: return
    if not (REPRO/'.lake/build/lib/lean/ComplementedSubspace.olean').is_file():
        mark('3_source_reproduction','FAILED CHECK'); raise RuntimeError('Successful build did not produce expected root')
    paths=run('rebuilt-search-path-after',[BIN/'lake.exe','--no-cache','env',sys.executable,'-c',
      'import os; print("\\n".join(k+"="+v for k,v in os.environ.items() if k.startswith(("LEAN","LAKE","MATHLIB"))))'],REPRO,env,timeout=180)
    if paths['exit_code']!=0 or str(PROJECT) in (EVIDENCE/paths['stdout']).read_text():
        raise RuntimeError('Could not establish rebuilt replay path isolation')
    mark('4_rebuilt_fresh_replay','RUNNING')
    replay=run('rebuilt-fresh-replay',[BIN/'lake.exe','--no-cache','env',BIN/'leanchecker.exe','--fresh','--verbose','ComplementedSubspace'],REPRO,env)
    mark('4_rebuilt_fresh_replay',replay['status'])
    # Even a rejected replay must preserve and investigate endpoint identities independently.
    checks=[('endpoint-types-and-axioms',EVIDENCE/'EndpointChecks.lean'),
            ('printed-mathematical-definitions',EVIDENCE/'PrintDefinitions.lean'),
            ('review-formulation-identity',REPRO/'MainTheoremReview.lean')]
    results=[]
    for label,file in checks:
        results.append(run(label,[BIN/'lake.exe','--no-cache','env',BIN/'lean.exe','-j1','-M8192',file],REPRO,env,timeout=600))
    mark('5_endpoint_definition_axiom_checks','PASS' if all(r['exit_code']==0 for r in results) else 'FAILED CHECK')

if __name__=='__main__':
    try: main()
    except Exception:
        import traceback
        (EVIDENCE/'rebuild-runner-error.txt').write_text(traceback.format_exc(),encoding='utf-8')
        raise
