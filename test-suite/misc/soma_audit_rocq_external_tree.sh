#!/usr/bin/env bash
# Until external source-tree membership is traced, both direct and imported
# local libraries outside the project remain uncertified, even on warm hits.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
python3 - <<'PY'
import os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-rocq-external-') as tmp:
    outer=pathlib.Path(tmp).resolve()
    for mode in os.environ.get('SOMA_AUDIT_EXTERNAL_MODES','direct,imported,nested-link').split(','):
        root=outer/mode
        root.mkdir();(root/'tests').mkdir()
        external=outer/(mode+'-library')
        external.mkdir()
        library_root = external
        if mode == 'nested-link':
            library_root = root/'vendor'
            library_root.mkdir()
            (library_root/'extra').symlink_to(external, target_is_directory=True)
        (library_root/'_RocqProject').write_text('-Q . mylib\n')
        (library_root/'A.v').write_text('Definition from_library := 1.\n')
        (root/'soma.toml').write_text('[project]\nname="external_trace"\nversion="0.1.0"\n')
        (root/'.gitignore').write_text('.soma-cache/\n')
        # TemporaryDirectory uses ordinary path bytes, so a Soma literal is safe.
        library='Rocq Library "mylib" in "'+str(library_root)+'".\nFrom mylib Require Import A.\nvalue := from_library.\n'
        if mode in ['direct','nested-link']:
            (root/'tests/main.soma').write_text(library)
        else:
            (root/'lib.soma').write_text(library)
            (root/'tests/main.soma').write_text('Import lib.\nvalue.\n')
        (root/'tests/main.exp').write_text('Theorem checked : value = 1. Proof. reflexivity. Qed.\n')
        for args in [['init','-q'],['add','.'],['-c','user.name=Audit','-c','user.email=audit@example.invalid','commit','-qm','fixture']]:
            subprocess.run(['git',*args],cwd=root,check=True)
        env=dict(os.environ,SOMA_CACHE=str(outer/(mode+'-store')),XDG_CACHE_HOME=str(outer/(mode+'-xdg')))
        def soma(*args):
            return subprocess.run(['soma','test',*args],cwd=root,env=env,text=True,capture_output=True,timeout=120)
        first=soma('--full')
        assert first.returncode==0,(mode,first.stdout,first.stderr)
        # A warm completed entry still cannot certify the external selection.
        second=soma('--full')
        assert second.returncode==0,(mode,second.stdout,second.stderr)
        selected=soma('--changedSince','HEAD','--listTests')
        assert selected.returncode==0 and selected.stdout.splitlines()==['tests/main.soma'],(mode,selected.stdout,selected.stderr)
        # Existing file hashes alone would miss this newly added source.
        (external/'B.v').write_text('Definition broken := missing_external_name.\n')
        selected=soma('--changedSince','HEAD','--listTests')
        assert selected.stdout.splitlines()==['tests/main.soma'],(mode,selected.stdout,selected.stderr)
        failed=soma('--changedSince','HEAD')
        assert failed.returncode!=0,(mode,failed.stdout,failed.stderr)
print('External local library trees never falsely certify direct or transitive test skips: passed')
PY
