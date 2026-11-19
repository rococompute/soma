#!/usr/bin/env bash
# A failed Load caught by Fail is still a filesystem dependency: creating
# that source makes Fail itself fail and must not reuse a former success.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0 SOMA_PROOF_JOBS=0
python3 - <<'PY'
import os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-failed-load-') as tmp:
    outer=pathlib.Path(tmp).resolve()
    for mode in os.environ.get('SOMA_AUDIT_FAILED_LOAD_MODES','direct,imported,library').split(','):
        root=outer/mode;root.mkdir()
        (root/'soma.toml').write_text('[project]\nname="failed_load"\nversion="0.1.0"\n')
        missing=outer/(mode+'-missing.v')
        command='Fail Load "'+str(missing)+'".\n'
        if mode=='imported':
            (root/'lib.soma').write_text(command+'value : nat := 1.\n')
            (root/'main.soma').write_text('Import lib.\nvalue.\n')
            args=['rocq','c','-q','main.soma']
        elif mode=='library':
            (root/'vendor').mkdir();(root/'vendor/_RocqProject').write_text('-Q . mylib\n')
            (root/'vendor/A.v').write_text(command+'Definition result := 1.\n')
            (root/'main.soma').write_text('Rocq Library "mylib" in "vendor".\nFrom mylib Require Import A.\nresult.\n')
            args=['rocq','c','-q','main.soma']
        else:
            (root/'helper.soma').write_text('local_value : nat := 0.\n')
            (root/'main.soma').write_text('Import helper.\n'+command+'main : nat := 1.\n')
            args=['soma','build','main.soma']
        env=dict(os.environ,SOMA_CACHE=str(outer/(mode+'-store')),XDG_CACHE_HOME=str(outer/(mode+'-xdg')))
        first=subprocess.run(args,cwd=root,env=env,text=True,capture_output=True,timeout=90)
        assert first.returncode==0,(mode,first.stdout,first.stderr)
        missing.write_text('Definition appeared := 2.\n')
        second=subprocess.run(args,cwd=root,env=env,text=True,capture_output=True,timeout=90)
        assert second.returncode!=0,(mode,'failed Load absent-to-present was skipped',second.stdout,second.stderr)
        assert 'The command has not failed!' in second.stderr,(mode,'expected current-source Fail diagnostic',second.stdout,second.stderr)
print('Failed Load absent-to-present changes invalidate root/import/Rocq-library successes: passed')
PY
