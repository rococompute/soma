#!/usr/bin/env bash
# Git-ignored compiler inputs still invalidate an otherwise clean test receipt.
# Accept conservative refusal of an initially uncertifiable ignored config.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0 SOMA_PROOF_JOBS=0
python3 - <<'PY'
import json,os,pathlib,subprocess,tempfile
records=[]
try:
    with tempfile.TemporaryDirectory(prefix='soma-ignored-rule-inputs-') as tmp:
        outer=pathlib.Path(tmp).resolve()
        for mode in os.environ.get('SOMA_AUDIT_IGNORED_RULE_MODES','rule,suppressor,manifest,legacy').split(','):
            root=outer/mode;root.mkdir();(root/'lib').mkdir()
            manifest=root/'soma.toml'
            name='one' if mode=='manifest' else 'project'
            manifest.write_text('[project]\nname="'+name+'"\nversion="0.1.0"\n')
            expected='false' if mode=='suppressor' else '(negb false)'
            if mode=='manifest':
                (root/'one.ext').write_text('Notation "\'flag_literal\'" := true.\n')
                (root/'two.ext').write_text('Notation "\'flag_literal\'" := false.\n')
                (root/'main.soma').write_text('value : bool := flag_literal.\n')
            else:
                (root/'lib/item.soma').write_text('flag : bool := true.\n')
                (root/'main.soma').write_text('Import lib.item.\nvalue : bool := flag.\n')
            (root/'main.exp').write_text('Theorem expected : value = '+expected+'. Proof. reflexivity. Qed.\n')
            ignored={'rule':'lib/lib.ext','suppressor':'lib/lib.soma',
                     'manifest':'soma.toml','legacy':'lib/lib.lang'}[mode]
            if mode=='suppressor':(root/'lib/lib.ext').write_text('Notation "\'true\'" := false.\n')
            (root/'.gitignore').write_text('.soma-cache/\n*.vo\n*.glob\n.*.aux\n'+ignored+'\n')
            for args in [['init','-q'],['add','.'],['-c','user.name=Audit','-c','user.email=audit@example.invalid','commit','-qm','fixture']]:
                subprocess.run(['git',*args],cwd=root,check=True)
            env=dict(os.environ,SOMA_CACHE=str(outer/(mode+'-store')),XDG_CACHE_HOME=str(outer/(mode+'-xdg')))
            def run(label,args):
                p=subprocess.run(['soma',*args],cwd=root,env=env,text=True,capture_output=True,timeout=90)
                records.append(dict(mode=mode,step=label,exit=p.returncode,stdout=p.stdout,stderr=p.stderr))
                return p
            seed=run('seed full',['test','--full','main.soma'])
            assert seed.returncode==0,records[-1]
            # An implementation may retain a sound receipt or deliberately
            # decline one for inputs outside its snapshot coverage.
            clean=run('seed selection',['test','--changedSince','HEAD','--listTests','main.soma'])
            assert clean.returncode==0,records[-1]
            if mode=='manifest':manifest.write_text('[project]\nname="two"\nversion="0.1.0"\n')
            elif mode=='rule':(root/ignored).write_text('Notation "\'true\'" := false.\n')
            elif mode=='suppressor':(root/ignored).write_text('unused : nat := 123.\n')
            else:(root/ignored).write_text('(* obsolete extension filename must be reported *)\n')
            status=subprocess.run(['git','status','--porcelain'],cwd=root,text=True,capture_output=True,check=True).stdout
            assert status=='',(mode,'fixture must present no changed Git paths',status)
            selected=run('ignored input changed selection',['test','--changedSince','HEAD','--listTests','main.soma'])
            assert selected.returncode==0 and selected.stdout.splitlines()==['main.soma'],records[-1]
            checked=run('ignored input changed actual test',['test','--changedSince','HEAD','main.soma'])
            assert checked.returncode!=0,records[-1]
            if mode=='legacy':assert 'is not read' in checked.stderr,records[-1]
finally:
    for row in records:print(json.dumps(row))
print('Ignored new rules, source suppressors, manifest contents and legacy names cannot bypass test selection: passed')
PY
