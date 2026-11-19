#!/usr/bin/env bash
# Local-cache freshness, independent of donor restore: selected implicit
# rules and original source kind are actual compiler inputs.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0 SOMA_PROOF_JOBS=0
python3 - <<'PY'
import os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-implicit-rules-') as tmp:
    outer=pathlib.Path(tmp).resolve()
    for mode in os.environ.get('SOMA_AUDIT_RULE_MODES','added,unsuppressed,kind,orphan').split(','):
        root=outer/mode;root.mkdir();(root/'lib').mkdir()
        (root/'soma.toml').write_text('[project]\nname="project"\nversion="0.1.0"\n')
        env=dict(os.environ,XDG_CACHE_HOME=str(outer/(mode+'-xdg')))
        def run(expected=0):
            p=subprocess.run(['rocq','c','-q','main.soma'],cwd=root,env=env,text=True,capture_output=True,timeout=90)
            assert (p.returncode==0)==(expected==0),(mode,p.stdout,p.stderr)
            return p
        def item_compiled(p):return 'Compiling lib/item.soma ' in p.stderr
        rule='Notation "\'true\'" := false.\n'
        if mode=='kind':
            body='Definition flag : bool := true.\n'
            (root/'lib/lib.ext').write_text(body)
            (root/'lib/item.soma').write_text('value : bool := flag.\n')
            (root/'main.soma').write_text('Import lib.item.\nvalue.\n')
            assert '= true' in run().stdout
            (root/'lib/lib.soma').write_text(body)
            (root/'main.soma').write_text('Import lib.lib.\nlib_lang.flag.\n')
            changed=run()
            assert 'Compiling lib/lib.soma ' in changed.stderr,changed.stderr
            assert '= true' in changed.stdout
            continue
        (root/'lib/item.soma').write_text('flag : bool := true.\n')
        (root/'main.soma').write_text('Import lib.item.\nflag.\n')
        if mode=='unsuppressed':
            (root/'lib/lib.ext').write_text(rule)
            (root/'lib/lib.soma').write_text('unused : nat := 0.\n')
        assert '= true' in run().stdout
        assert not item_compiled(run()),'unchanged module should remain reusable'
        (root/'unrelated.soma').write_text('other : nat := 12.\n')
        assert not item_compiled(run()),'unrelated source body is not an implicit rule input'
        if mode=='added':
            (root/'lib/lib.ext').write_text(rule)
        elif mode=='unsuppressed':
            (root/'lib/lib.soma').write_text('unused : nat := 123.\n')
            assert not item_compiled(run()),'suppressed program body must not invalidate item'
            (root/'lib/lib.soma').unlink()
        else:
            (root/'lib/lib.exp').write_text('Theorem orphan : False. Proof. exact I. Qed.\n')
            failed=run(expected=1)
            assert 'does not exist' in failed.stderr,failed.stderr
            (root/'lib/lib.exp').unlink()
            assert '= true' in run().stdout,'removing orphan expectations should recover'
            continue
        changed=run()
        assert '= false' in changed.stdout,(mode,'stale implicit rules',changed.stdout,changed.stderr)
        assert item_compiled(changed),changed.stderr
        assert not item_compiled(run()),'new selected-rule state should become reusable'
print('In-place rule additions, suppressor removal, source kind and orphan expectations are checked; unrelated bodies stay cached: passed')
PY
