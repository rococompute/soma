#!/usr/bin/env bash
# No byte diff can represent a standalone build-root rename. Receipt scope
# must follow each entry point's actual root, preserving manifest/nested moves.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0 SOMA_PROOF_JOBS=0
python3 - <<'PY'
import os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-rule-receipts-') as tmp:
    outer=pathlib.Path(tmp).resolve()
    for mode in os.environ.get('SOMA_AUDIT_RECEIPT_MODES','standalone,manifest,nested').split(','):
        parent=outer/mode;parent.mkdir();root=parent/'alpha';root.mkdir()
        src=root/'tests' if mode=='nested' else root
        src.mkdir(exist_ok=True);(src/'lib').mkdir()
        if mode=='manifest':
            (root/'soma.toml').write_text('[project]\nname="project"\nversion="0.1.0"\n')
        if mode=='nested':
            # A plain standalone entry isolates its own fallback scope from
            # imported-module trace support, which is independent of this move.
            (src/'main.soma').write_text('value : bool := true.\n')
            (src/'main.exp').write_text('Theorem checked : value = true. Proof. reflexivity. Qed.\n')
        else:
            rule_name='project' if mode=='manifest' else src.name
            (src/(rule_name+'.ext')).write_text('Notation "\'true\'" := false.\n')
            (src/'lib/item.soma').write_text('flag : bool := true.\n')
            (src/'main.soma').write_text('Import lib.item.\nvalue : bool := flag.\n')
            (src/'main.exp').write_text('Theorem checked : value = false. Proof. reflexivity. Qed.\n')
        (root/'.gitignore').write_text('.soma-cache/\n')
        for args in [['init','-q'],['add','.'],['-c','user.name=Audit','-c','user.email=audit@example.invalid','commit','-qm','fixture']]:subprocess.run(['git',*args],cwd=root,check=True)
        entry='tests/main.soma' if mode=='nested' else 'main.soma'
        env=dict(os.environ,SOMA_CACHE=str(parent/'store'),XDG_CACHE_HOME=str(parent/'xdg'))
        def test(args,expected=0):
            p=subprocess.run(['soma','test',*args,entry],cwd=root,env=env,text=True,capture_output=True,timeout=90)
            assert (p.returncode==0)==(expected==0),(mode,p.stdout,p.stderr)
            return p
        seed=test(['--full'])
        selected_seed=test(['--changedSince','HEAD','--listTests'])
        assert selected_seed.stdout=='',(mode,'seed should certify zero diff',seed.stdout,seed.stderr,selected_seed.stdout,selected_seed.stderr)
        moved=parent/'beta';root.rename(moved);root=moved
        selected=test(['--changedSince','HEAD','--listTests']).stdout.splitlines()
        if mode=='standalone':
            assert selected==[entry],(mode,'fallback root rule changed without a file diff',selected)
            failed=test(['--changedSince','HEAD'],expected=1)
            assert 'true' in failed.stderr or 'false' in failed.stderr,failed.stderr
        else:
            assert selected==[],(mode,'equivalent actual entry root should remain certified',selected)
print('Receipt scope follows per-entry fallback rule identity; manifest and nested equivalent moves remain skippable: passed')
PY
