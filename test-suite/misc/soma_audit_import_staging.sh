#!/usr/bin/env bash
# Exercise real staged .vos interfaces and checked proof .vo publication,
# including parallel imports under nested logical module names.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0 SOMA_DEFER_PROOFS=1
python3 - <<'PY'
import os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-import-staging-') as tmp:
    root=pathlib.Path(tmp);(root/'models').mkdir()
    (root/'soma.toml').write_text('[project]\nname="staging"\nversion="0.1.0"\n')
    (root/'models/a.soma').write_text('first : nat := 2.\n')
    (root/'models/a.exp').write_text('Theorem first_checked : first = 2. Proof. reflexivity. Qed.\n')
    (root/'models/b.soma').write_text('second : nat := 5.\n')
    (root/'models/b.exp').write_text('Theorem second_checked : second = 5. Proof. reflexivity. Qed.\n')
    (root/'main.soma').write_text('Import models.a models.b.\nresult : nat := first + second.\nresult.\n')
    env=dict(os.environ,XDG_CACHE_HOME=str(root/'xdg'))
    def run(expected=0):
        p=subprocess.run(['rocq','c','-q','main.soma'],cwd=root,env=env,text=True,capture_output=True,timeout=90)
        assert (p.returncode==0)==(expected==0),(p.stdout,p.stderr)
        return p
    assert '= 7' in run().stdout
    for name in ['a','b']:
        assert (root/('.soma-cache/models/'+name+'.vo')).is_file()
        assert (root/('.soma-cache/models/'+name+'.stamp')).is_file()
    assert 'Compiling ' not in run().stderr,'checked imports should be reusable'
    (root/'models/a.exp').write_text('Theorem first_checked : first = 3. Proof. reflexivity. Qed.\n')
    failed=run(expected=1)
    assert 'first' in failed.stderr or 'proof' in failed.stderr,failed.stderr
    (root/'models/a.soma').write_text('first : nat := 3.\n')
    assert '= 8' in run().stdout
    assert 'Compiling ' not in run().stderr
    assert not list((root/'.soma-cache').rglob('.soma-import-*'))
    assert not list((root/'.soma-cache').rglob('.soma-spliced-*'))
    assert not list((root/'.soma-cache').rglob('.soma-stamp-*'))
print('Imported nested namespaces, deferred proof interfaces, failure/recovery and staged-output cleanup: passed')
PY
