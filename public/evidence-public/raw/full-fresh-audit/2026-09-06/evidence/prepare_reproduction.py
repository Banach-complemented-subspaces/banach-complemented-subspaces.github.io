"""Copy immutable source into physically independent directories, retaining no Lean artifacts."""
from audit_runner import *
import shutil, stat

def safe_tree(root):
    problems=[]
    for parent, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {'.lake','.cache','node_modules'}]
        for name in dirs+files:
            p=Path(parent)/name
            if p.is_symlink() or p.is_junction() or p.lstat().st_file_attributes & stat.FILE_ATTRIBUTE_REPARSE_POINT:
                problems.append(str(p))
    if root.is_symlink() or root.is_junction(): problems.append(str(root))
    if problems: raise RuntimeError('Reparse/symlink paths require review: '+repr(problems))

def main():
    if REPRO.exists(): raise RuntimeError('Refusing to reuse a reproduction directory')
    REPRO.mkdir(parents=True)
    for p,h in project_files():
        target=REPRO/p; target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(PROJECT/p,target)
        if sha(target)!=h: raise RuntimeError('Source copy mismatch: '+p)
    for name in ['README.md','BUILDING.md']:
        shutil.copyfile(PROJECT/name,REPRO/name)
    manifest('reproduction-source-manifest-before.sha256',REPRO,[p for p,h in project_files()])
    packages=json.loads((PROJECT/'lake-manifest.json').read_text())['packages']
    revision_rows=[]; dep_hashes=[]
    for pkg in packages:
        name=pkg['name']; src=PROJECT/'.lake/packages'/name
        if pkg['type']!='git': raise RuntimeError('Non-git external dependency requires explicit path review: '+name)
        safe_tree(src)
        if not (src/'.git').is_dir(): raise RuntimeError('Worktree/external git dir not permitted: '+name)
        if (src/'.git/objects/info/alternates').exists() or (src/'.git/commondir').exists():
            raise RuntimeError('Shared git objects require explicit isolation: '+name)
        head=run('dependency-'+name+'-head',[GIT,'rev-parse','HEAD'],src,timeout=120)
        status=run('dependency-'+name+'-status',[GIT,'status','--porcelain=v1','--untracked-files=normal'],src,timeout=120)
        tracked=run('dependency-'+name+'-tracked',[GIT,'ls-files','-z'],src,timeout=120)
        if any(r['exit_code']!=0 for r in [head,status,tracked]): raise RuntimeError('Dependency identity command failed: '+name)
        actual=(EVIDENCE/head['stdout']).read_text().strip()
        if actual!=pkg['rev']: raise RuntimeError('Manifest/checkout mismatch: '+name)
        dst=REPRO/'.lake/packages'/name
        shutil.copytree(src,dst,ignore=shutil.ignore_patterns('.lake','.cache','node_modules'),copy_function=shutil.copyfile)
        safe_tree(dst)
        tracked_names=(EVIDENCE/tracked['stdout']).read_bytes().decode('utf-8').split('\0')
        records=[]
        for rel in filter(None,tracked_names):
            original=src/rel; copied=dst/rel
            if not original.is_file(): raise RuntimeError('Tracked source is not a normal file: '+str(original))
            if not copied.is_file(): raise RuntimeError('Tracked source excluded unexpectedly: '+name+'/'+rel)
            h=sha(original)
            if sha(copied)!=h: raise RuntimeError('Dependency source copy mismatch: '+name+'/'+rel)
            records.append((rel,h)); dep_hashes.append((name+'/'+rel,h))
        revision_rows.append(dict(name=name,url=pkg['url'],manifest_revision=pkg['rev'],actual_revision=actual,
            original_path=str(src),reproduction_path=str(dst),tracked_files=len(records),
            working_tree_status=(EVIDENCE/status['stdout']).read_text(),
            git_repository_copied_independently=True,shared_objects=False))
    save('dependency-revisions.json',revision_rows)
    (EVIDENCE/'dependency-revisions.txt').write_text('\n\n'.join(json.dumps(r,indent=2) for r in revision_rows),encoding='utf-8')
    (EVIDENCE/'dependency-source-manifest-before.sha256').write_text(''.join(f'{h}  {p}\n' for p,h in dep_hashes),encoding='utf-8')
    forbidden=[]; source_files=[]
    for parent,dirs,files in os.walk(REPRO):
        dirs[:] = [d for d in dirs if d!='.git']
        for name in files:
            p=Path(parent)/name
            if p.suffix in {'.olean','.ilean','.ir','.o','.obj','.a','.dll','.so','.dylib'}: forbidden.append(str(p.relative_to(REPRO)))
            if p.suffix=='.lean': source_files.append(str(p.relative_to(REPRO)))
    if forbidden: raise RuntimeError('Pre-existing non-toolchain artifacts in isolated copy: '+repr(forbidden))
    save('clean-state.json',{'checked':now(),'reproduction':str(REPRO),'root_build_exists':(REPRO/'.lake/build').exists(),
        'dependency_builds':[str(p) for p in (REPRO/'.lake/packages').glob('*/.lake/build')],
        'preexisting_compiled_lean_or_native_artifacts':forbidden,'lean_source_files':len(source_files),
        'symlinks_or_junctions':[], 'copy_method':'byte copies; no hardlinks or shared git objects',
        'retained_nonlean_inputs':'Pinned tracked ProofWidgets JavaScript and its source-tree lake.trace inputs; no Lean compiled artifacts retained.',
        'retained_toolchain':str(TOOLCHAIN)})
    (EVIDENCE/'clean-state.txt').write_text((EVIDENCE/'clean-state.json').read_text(),encoding='utf-8')
    print('Independent source copy ready; '+str(len(dep_hashes))+' dependency source files hashed.',flush=True)

if __name__=='__main__':
    try: main()
    except Exception:
        import traceback
        (EVIDENCE/'prepare-reproduction-error.txt').write_text(traceback.format_exc(),encoding='utf-8')
        raise
