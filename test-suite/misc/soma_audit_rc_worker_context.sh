#!/usr/bin/env bash
# Real driver/worker binaries in private paths; only the selected worker has
# a fallback HOME/XDG sidecar. No installed executable/config is modified.
set -euo pipefail
export PATH="$BIN:$PATH"
python3 - <<'PY'
import json,os,pathlib,shutil,subprocess,tempfile
bin=pathlib.Path(os.environ['BIN']).resolve()
runtime=pathlib.Path(os.environ['ROCQRUNTIMELIB']).resolve()
observe=os.environ.get('SOMA_RC_AUDIT_OBSERVE')=='1';records=[];failures=[]
def expect(ok,label):
    if not ok:
        failures.append(label)
        if not observe:raise AssertionError(label)
with tempfile.TemporaryDirectory(prefix='soma-worker-rc-') as tmp:
    work=pathlib.Path(tmp).resolve();prefix=work/'install';(prefix/'bin').mkdir(parents=True)
    lib=prefix/'lib';lib.mkdir();private=lib/'soma-runtime';private.mkdir()
    # Findlib sees the actual original package layout, but selects our copied
    # worker executable and its private adjacent fallback configuration.
    for child in runtime.iterdir():
        if child.name not in ['rocqworker','coq_environment.txt']:
            (private/child.name).symlink_to(child.resolve(),target_is_directory=child.is_dir())
    shutil.copy2(bin/'soma',prefix/'bin/soma')
    shutil.copy2(runtime/'rocqworker',private/'rocqworker')
    worker_home=work/'worker-home';worker_home.mkdir()
    worker_config=work/'worker-config';(worker_config/'coq').mkdir(parents=True)
    (private/'coq_environment.txt').write_text('HOME="'+str(worker_home)+'"\nXDG_CONFIG_HOME="'+str(worker_config)+'"\n')
    app=work/'app';app.mkdir();(app/'main.soma').write_text('value : nat := 1.\n')
    env=dict(os.environ,ROCQRUNTIMELIB=str(private),XDG_CACHE_HOME=str(work/'cache'),SOMA_CACHE=str(work/'shared'),
             OCAMLPATH=str(lib)+os.pathsep+os.environ.get('OCAMLPATH',''),SOMA_MIRAGE_BUILD='0',SOMA_OCAML_BUILD='0')
    for key in ['HOME','XDG_CONFIG_HOME','HOMEDRIVE','HOMEPATH','USERPROFILE','SOMA_PROJECT_ROOT','SOMA_PROJECT_CACHE','SOMA_BUILD_ROOT','ROCQPATH','COQPATH']:
        env.pop(key,None)
    def run(stage,args,success=True):
        p=subprocess.run([str(prefix/'bin/soma')]+args,cwd=app,env=env,text=True,capture_output=True,timeout=90)
        records.append(dict(stage=stage,args=args,exit=p.returncode,stdout=p.stdout,stderr=p.stderr))
        expect((p.returncode==0)==success,stage+': unexpected exit '+str(p.returncode));return p
    run('worker-no-rc-build',['build','main.soma']);run('worker-no-rc-fresh',['build','--check-fresh','main.soma'])
    rc=worker_config/'coq/coqrc';rc.write_text('ThisWorkerRcMustBeExecuted.\n')
    run('worker-only-rc-stale',['build','--check-fresh','main.soma'],False)
    p=run('worker-only-rc-executed',['build','main.soma'],False)
    expect('ThisWorkerRcMustBeExecuted' in p.stderr,'worker-only rc was skipped')
    rc.unlink();run('worker-rc-removed-build',['build','main.soma']);run('worker-rc-removed-fresh',['build','--check-fresh','main.soma'])
    # With XDG absent in its sidecar, the same selected worker uses HOME.
    (private/'coq_environment.txt').write_text('HOME="'+str(worker_home)+'"\n')
    run('worker-home-no-rc-build',['build','main.soma']);run('worker-home-no-rc-fresh',['build','--check-fresh','main.soma'])
    rc=worker_home/'.coqrc';rc.write_text('ThisWorkerHomeRcMustBeExecuted.\n')
    run('worker-home-rc-stale',['build','--check-fresh','main.soma'],False)
    p=run('worker-home-rc-executed',['build','main.soma'],False)
    expect('ThisWorkerHomeRcMustBeExecuted' in p.stderr,'worker-only HOME rc was skipped')
report=os.environ.get('SOMA_RC_AUDIT_REPORT')
if report:pathlib.Path(report).write_text(json.dumps(dict(records=records,failures=failures),indent=2)+'\n')
if observe:print('observed worker rc mismatches:',json.dumps(failures))
else:print('actual selected worker-only XDG/HOME sidecar rc appearance/execution/removal: passed')
PY
