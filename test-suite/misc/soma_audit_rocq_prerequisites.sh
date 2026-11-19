#!/usr/bin/env bash
# Selected prerequisites are actual compiler inputs and part of completion
# identity. Repeated and parallel consumers must reuse the right generation.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
python3 - <<'PY'
import concurrent.futures,os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-rocq-prerequisites-') as tmp:
    root=pathlib.Path(tmp)
    (root/'soma.toml').write_text('[project]\nname="prerequisites"\nversion="0.1.0"\n')
    alpha=root/'alpha';alpha.mkdir()
    (alpha/'_RocqProject').write_text('-Q . alpha\n')
    (alpha/'A.v').write_text('Definition from_alpha := 1.\n')
    for package,plus in [('beta',1),('gamma',2)]:
        lib=root/package;lib.mkdir()
        (lib/'_RocqProject').write_text('-Q . '+package+'\n')
        (lib/'B.v').write_text('From alpha Require Import A.\nDefinition result := from_alpha + '+str(plus)+'.\n')
        declarations='Rocq Library "alpha" in "alpha".\nRocq Library "'+package+'" in "'+package+'".\n'
        (root/(package+'.soma')).write_text(declarations+'From '+package+' Require Import B.\nresult.\n')
        (root/(package+'-repeat.soma')).write_text(declarations+'Rocq Library "'+package+'" in "'+package+'".\nFrom '+package+' Require Import B.\nresult.\n')
    env=dict(os.environ,XDG_CACHE_HOME=str(root/'xdg'))
    def run(file):
        p=subprocess.run(['rocq','c','-q',file],cwd=root,env=env,text=True,capture_output=True,timeout=90)
        assert p.returncode==0,(file,p.stdout,p.stderr)
        return p
    def entries(package): return {p.parent.name for p in (root/'.soma-cache/rocq').glob(package+'-*/theories')}
    # Different consumers compile safely in parallel with the same prerequisite.
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        first=list(pool.map(run,['beta.soma','gamma.soma']))
    assert '= 2' in first[0].stdout and '= 3' in first[1].stdout
    beta1=entries('beta');gamma1=entries('gamma')
    assert len(beta1)==len(gamma1)==1,(beta1,gamma1)
    for file in ['beta.soma','beta-repeat.soma','gamma-repeat.soma']:
        assert 'Rocq: compiling' not in run(file).stderr,file
    assert entries('beta')==beta1 and entries('gamma')==gamma1
    (alpha/'A.v').write_text('Definition from_alpha := 2.\n')
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        second=list(pool.map(run,['beta.soma','gamma.soma']))
    assert '= 3' in second[0].stdout and '= 4' in second[1].stdout
    assert 'beta/B.v' in second[0].stderr and 'gamma/B.v' in second[1].stderr
    assert len(entries('beta'))==len(entries('gamma'))==2
    assert beta1 < entries('beta') and gamma1 < entries('gamma'),'old entries must remain archived'
    assert 'Rocq: compiling' not in run('beta-repeat.soma').stderr
print('Rocq prerequisite paths, dependency-bound keys, stable reselection and parallel generations: passed')
PY
