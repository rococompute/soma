#!/usr/bin/env bash
# Actual source Load bypasses the compiled-library table. Unrepresented
# source loads must not keep root builds or imported definitions fresh.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0 SOMA_PROOF_JOBS=0
python3 - <<'PY'
import os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-loaded-source-') as tmp:
    outer=pathlib.Path(tmp).resolve()
    for mode in os.environ.get('SOMA_AUDIT_LOAD_MODES','direct,imported,nested,companion').split(','):
        root=outer/mode;root.mkdir()
        (root/'soma.toml').write_text('[project]\nname="loaded_source"\nversion="0.1.0"\n')
        external=outer/(mode+'-defs.v')
        external.write_text('Definition loaded : nat := 1.\n')
        (root/'helper.soma').write_text('local_value : nat := 0.\n')
        statement='Load "'+str(external)+'".\n'
        if mode=='imported':
            (root/'lib.soma').write_text(statement+'value : nat := loaded.\n')
            (root/'main.soma').write_text('Import lib.\nvalue.\n')
        elif mode=='nested':
            (root/'main.ext').write_text(statement)
            (root/'main.soma').write_text('Import helper.\nmain : nat := loaded.\n')
        elif mode=='companion':
            (root/'main.ext').write_text('Definition loaded : nat := 1.\n')
            (root/'main.soma').write_text('Import helper.\nmain : nat := loaded.\n')
        else:
            (root/'main.soma').write_text('Import helper.\n'+statement+'main : nat := loaded.\n')
        env=dict(os.environ,SOMA_CACHE=str(outer/(mode+'-store')),XDG_CACHE_HOME=str(outer/(mode+'-xdg')))
        def run(args,expected=0):
            p=subprocess.run(args,cwd=root,env=env,text=True,capture_output=True,timeout=90)
            assert (p.returncode==0)==(expected==0),(mode,args,p.stdout,p.stderr)
            return p
        if mode=='imported':
            first=run(['rocq','c','-q','main.soma'])
            assert '= 1' in first.stdout
        else:
            run(['soma','build','main.soma'])
        if mode=='companion':
            run(['soma','build','--check-fresh','main.soma'])
            (root/'main.ext').write_text('Definition loaded : nat := 2.\n')
        else:
            external.write_text('Definition loaded : nat := 2.\n')
        if mode=='imported':
            # Bypass whole-build caching to isolate imported stamp freshness.
            changed=run(['rocq','c','-q','main.soma'])
            assert '= 2' in changed.stdout,(mode,'imported Load reused stale definitions',changed.stdout,changed.stderr)
        else:
            run(['soma','build','--check-fresh','main.soma'],expected=1)
            run(['soma','build','main.soma'])
print('Source Load edits invalidate direct/imported/nested builds while captured companions stay reusable: passed')
PY
