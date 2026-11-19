#!/usr/bin/env bash
# Source-unit membership and implicit extension rules are donor inputs too.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_OCAML_BUILD=0 SOMA_MIRAGE_BUILD=0 SOMA_PROOF_JOBS=0
python3 - <<'PY'
import json,os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-donor-rules-') as tmp:
    outer=pathlib.Path(tmp)
    env=dict(os.environ,SOMA_CACHE=str(outer/'shared'),XDG_CACHE_HOME=str(outer/'xdg'))
    records=[]
    def project(name,rules=False,shadow=False):
        root=outer/name;(root/'lib').mkdir(parents=True)
        (root/'soma.toml').write_text('[project]\nname="rules"\nversion="0.1.0"\n')
        (root/'lib/item.soma').write_text('flag : bool := true.\n')
        (root/'main.soma').write_text('Import lib.item.\nflag.\n')
        if rules:(root/'lib/lib.ext').write_text('Notation "\'true\'" := false.\n')
        if shadow:(root/'lib/lib.soma').write_text('unused : nat := 1.\n')
        return root
    def build(root,expected):
        run=subprocess.run(['soma','build','-v','main.soma'],cwd=root,env=env,text=True,capture_output=True,timeout=90)
        records.append(dict(case=root.name,exit=run.returncode,stdout=run.stdout,stderr=run.stderr))
        assert run.returncode==0,(root,run.stdout,run.stderr)
        assert '= '+expected in run.stdout,(root,expected,run.stdout,run.stderr)
    build(project('no-folder-rule'), 'true')
    build(project('added-folder-rule',rules=True), 'false')
    # Removing the source-unit suppressor enables a pre-existing rule whose
    # bytes did not change; content-only non-Soma inputs cannot detect this.
    build(project('shadowed-folder-rule',rules=True,shadow=True), 'true')
    build(project('removed-source-suppressor',rules=True), 'false')
    print(json.dumps(records,indent=2))
    print('implicit folder-rule additions and source suppressor membership: passed')
PY
