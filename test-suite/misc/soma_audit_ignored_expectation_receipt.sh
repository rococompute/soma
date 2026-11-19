#!/usr/bin/env bash
# An optional expectation is a known compiler input even when Git ignores it.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0 SOMA_PROOF_JOBS=0
python3 - <<'PY'
import os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-ignored-expectation-') as tmp:
    outer=pathlib.Path(tmp).resolve();root=outer/'app';root.mkdir();(root/'tests').mkdir()
    (root/'soma.toml').write_text('[project]\nname="paired"\nversion="0.1.0"\n')
    (root/'.gitignore').write_text('.soma-cache/\n*.exp\n')
    (root/'tests/main.soma').write_text('value : nat := 1.\n')
    for args in [['init','-q'],['add','.'],['-c','user.name=Audit','-c','user.email=audit@example.invalid','commit','-qm','fixture']]:subprocess.run(['git',*args],cwd=root,check=True)
    env=dict(os.environ,SOMA_CACHE=str(outer/'store'),XDG_CACHE_HOME=str(outer/'xdg'))
    def run(args,expected=0):
        p=subprocess.run(['soma','test',*args],cwd=root,env=env,text=True,capture_output=True,timeout=90)
        assert (p.returncode==0)==(expected==0),(args,p.stdout,p.stderr)
        return p
    run(['--full']);assert run(['--changedSince','HEAD','--listTests']).stdout==''
    expectation=root/'tests/main.exp'
    expectation.write_text('Theorem impossible : False. Proof. exact I. Qed.\n')
    assert subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True)==''
    assert run(['--changedSince','HEAD','--listTests']).stdout=='tests/main.soma\n'
    failed=run(['--changedSince','HEAD'],expected=1)
    assert 'False' in failed.stderr,failed.stderr
    expectation.write_text('Theorem checked : value = 1. Proof. reflexivity. Qed.\n')
    accepted=run(['--changedSince','HEAD'])
    assert 'next run will include' in accepted.stderr,accepted.stderr
    assert run(['--changedSince','HEAD','--listTests']).stdout=='tests/main.soma\n'
    expectation.unlink()
    run(['--full']);assert run(['--changedSince','HEAD','--listTests']).stdout==''
print('Ignored paired expectations select tests, check actual proofs, decline incomplete receipts and recover ordinary warm skips: passed')
PY
