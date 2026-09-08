"""Read-only checks after compilation; separate outputs permit overlap with replay."""
from audit_runner import *
from concurrent.futures import ThreadPoolExecutor

def main():
    build=json.loads((EVIDENCE/'source-rebuild.command.json').read_text())
    if build.get('exit_code')!=0 or not build.get('ended'):
        raise RuntimeError('Compilation must have completed before source/input checks')
    jobs=[
        ('source-identity-and-placeholder-scan',[sys.executable,'-B',EVIDENCE/'check_identity_and_scan.py']),
        ('resolved-build-input-check',[sys.executable,'-B',EVIDENCE/'check_resolved_build_inputs.py',
             '--output-dir',EVIDENCE/'resolved-build-inputs']),
    ]
    with ThreadPoolExecutor(max_workers=2) as executor:
        futures=[executor.submit(run,label,args,ROOT,env_base(),1200) for label,args in jobs]
        results=[future.result() for future in futures]
    save('supplementary-native-results.json',results)

if __name__=='__main__':
    main()
