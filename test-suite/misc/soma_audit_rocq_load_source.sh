#!/usr/bin/env bash
# A Rocq compiler child may Load other source. Propagate those actual inputs
# and never reuse an unsupported/incomplete generation's stale definitions.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0 SOMA_PROOF_JOBS=0
python3 - <<'PY'
import os,pathlib,subprocess,tempfile
with tempfile.TemporaryDirectory(prefix='soma-rocq-loaded-source-') as tmp:
    outer=pathlib.Path(tmp).resolve()
    for mode in ['direct','nested']:
        root=outer/mode;root.mkdir();(root/'vendor').mkdir()
        (root/'soma.toml').write_text('[project]\nname="rocq_load"\nversion="0.1.0"\n')
        leaf=outer/(mode+'-leaf.v');leaf.write_text('Definition external_value := 1.\n')
        loaded=leaf
        if mode=='nested':
            loaded=outer/'nested-wrapper.v';loaded.write_text('Load "'+str(leaf)+'".\n')
        (root/'vendor/_RocqProject').write_text('-Q . mylib\n')
        (root/'vendor/A.v').write_text('Load "'+str(loaded)+'".\nDefinition result := external_value.\n')
        (root/'main.soma').write_text('Rocq Library "mylib" in "vendor".\nFrom mylib Require Import A.\nresult.\n')
        env=dict(os.environ,XDG_CACHE_HOME=str(outer/(mode+'-xdg')))
        def run(expected=0):
            p=subprocess.run(['rocq','c','-q','main.soma'],cwd=root,env=env,text=True,capture_output=True,timeout=90)
            assert (p.returncode==0)==(expected==0),(mode,p.stdout,p.stderr)
            return p
        assert '= 1' in run().stdout
        originals=list((root/'.soma-cache/rocq').glob('*/src/A.vo'));assert len(originals)==1
        original=originals[0]
        assert '= 1' in run().stdout,'unchanged invocation must still work'
        leaf.write_text('Definition external_value := 2.\n')
        changed=run()
        assert '= 2' in changed.stdout,(mode,'Rocq source Load reused stale definitions',changed.stdout,changed.stderr)
        assert original.is_file(),'prior live artifact was removed'
        generations=list((root/'.soma-cache/rocq').glob('*/src/A.vo'))
        assert len(generations)>=3,'unsupported Load should use fresh immutable generations'
        original.write_bytes(b'corrupt former completed artifact')
        rejected=run(expected=1)
        assert 'provenance' in rejected.stderr or 'changed' in rejected.stderr,rejected.stderr
print('Rocq child direct/nested Load uses current bytes, retains old generations and rejects corrupted artifacts: passed')
PY
