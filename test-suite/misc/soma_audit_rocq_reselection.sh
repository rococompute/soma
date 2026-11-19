#!/usr/bin/env bash
# Retained immutable entries are archives, never alternate search roots for
# modules removed from the currently selected logical theory.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
python3 - <<'PY'
import os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-rocq-reselection-') as tmp:
    root=pathlib.Path(tmp)
    (root/'soma.toml').write_text('[project]\nname="selection"\nversion="0.1.0"\n')
    vendor=root/'vendor';vendor.mkdir()
    (vendor/'_RocqProject').write_text('-Q . mylib\n')
    (vendor/'A.v').write_text('Definition current := 1.\n')
    (vendor/'Gone.v').write_text('Definition disappeared := 42.\n')
    nested=root/'nested';nested.mkdir()
    (nested/'_RocqProject').write_text('-Q . mylib.Inner\n')
    (nested/'Kept.v').write_text('Definition retained := 7.\n')
    (root/'dummy.soma').write_text('dummy := 0.\n')
    declaration='Rocq Library "mylib" in "vendor".\n'
    (root/'warm.soma').write_text(declaration+'Rocq Library "nested" in "nested".\nFrom mylib Require Import A.\ncurrent.\n')
    # The local import initializes persisted load paths before reselection.
    (root/'check.soma').write_text('Import dummy.\n'+declaration+'From mylib Require Import Gone.\ndisappeared.\n')
    (root/'nested.soma').write_text('Import dummy.\n'+declaration+'From mylib.Inner Require Import Kept.\nretained.\n')
    env=dict(os.environ,XDG_CACHE_HOME=str(root/'xdg'))
    def run(file,expected=0):
        p=subprocess.run(['rocq','c','-q',file],cwd=root,env=env,text=True,capture_output=True,timeout=90)
        assert (p.returncode==0)==(expected==0),(file,p.stdout,p.stderr)
        return p
    assert '= 1' in run('warm.soma').stdout
    before={p for p in (root/'.soma-cache/rocq').glob('*/src/Gone.vo')}
    assert len(before)==1
    (vendor/'Gone.v').unlink();(vendor/'A.v').write_text('Definition current := 2.\n')
    assert '= 2' in run('warm.soma').stdout
    rejected=run('check.soma',expected=1)
    assert 'Gone' in rejected.stderr,rejected.stderr
    assert all(p.is_file() for p in before),'archive entry was deleted'
    assert '= 7' in run('nested.soma').stdout,'independent nested theory was retired'
    rows=(root/'.soma-cache/load-paths').read_text().splitlines()
    assert sum(row.startswith('mylib ') for row in rows)==1,rows
    assert sum(row.startswith('mylib.Inner ') for row in rows)==1,rows
print('Rocq current-prefix reselection rejects removed modules and preserves archived/nested entries: passed')
PY
