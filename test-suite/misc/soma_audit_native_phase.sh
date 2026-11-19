#!/usr/bin/env bash
# Real kernel, extraction, native Dune and executable; only the opam command
# boundary is logged. No native tool or SDK validation may be skipped.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
export SOMA_TEST_PHASE_WORK="$WORK"
python3 - <<'PY'
import json, os, pathlib, shutil, subprocess, time
work=pathlib.Path(os.environ['SOMA_TEST_PHASE_WORK']).resolve()
app=work/'application'; app.mkdir()
tools=work/'tools'; tools.mkdir()
real_opam=shutil.which('opam'); assert real_opam
wrapper=tools/'opam'
wrapper.write_text('#!'+shutil.which('python3')+'\n'+
    'import json, os, sys\n'+
    'with open(os.environ["SOMA_TEST_PHASE_CALLS"],"a") as log: log.write(json.dumps(sys.argv[1:])+"\\n")\n'+
    'if sys.argv[1:2]==["exec"] and os.path.exists(os.environ["SOMA_TEST_PHASE_FAIL"]): sys.exit(41)\n'+
    'if sys.argv[1:2]==["exec"] and os.path.exists(os.environ["SOMA_TEST_PHASE_MUTATE"]):\n'+
    ' spec=json.load(open(os.environ["SOMA_TEST_PHASE_MUTATE"])); os.unlink(os.environ["SOMA_TEST_PHASE_MUTATE"]); open(spec["path"],"w").write(spec["text"])\n'+
    'os.execv('+repr(real_opam)+', ['+repr(real_opam)+']+sys.argv[1:])\n')
wrapper.chmod(0o755)
(app/'soma.toml').write_text('[project]\nname="native_phase_probe"\nversion="0.1.0"\n')
source=app/'main.soma'; original='Import succ.\nmain : string := to_string (succ 0) ++ " " ++ to_string (succ 41).\n'
source.write_text(original)
(app/'succ.definition').write_text('succ : nat -> nat.\n')
foreign=app/'succ.ml'; foreign.write_text('let succ (n : Soma_nat.nat) : Soma_nat.nat = n + 1\n')
env=dict(os.environ,PATH=str(tools)+os.pathsep+os.environ['PATH'],
    SOMA_OCAML_SWITCH=os.environ.get('SOMA_OCAML_SWITCH',str(pathlib.Path.home()/'.cache/soma/ocaml')),
    XDG_CACHE_HOME=str(work/'cache'),XDG_CONFIG_HOME=str(work/'config'),
    SOMA_CACHE=str(work/'shared'),SOMA_TEST_PHASE_CALLS=str(work/'calls'),SOMA_TEST_PHASE_FAIL=str(work/'fail'),
    SOMA_TEST_PHASE_MUTATE=str(work/'mutate'))
# HOME rc files would intentionally make the supported subset ineligible.
for name in ['.coqrc','.coqrc.*']:
    assert not list(pathlib.Path.home().glob(name)), 'run with an rc-free test HOME'
compiler=shutil.which('soma'); assert compiler
measurements=[]
def invoke(command,ok=True):
    started=time.monotonic();p=subprocess.run([compiler]+command,cwd=app,env=env,text=True,capture_output=True,timeout=180)
    measurements.append({'argv':command,'seconds':time.monotonic()-started,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    assert (p.returncode==0)==ok,(command,p.stdout,p.stderr)
    return p

def build(hit=None,ok=True):
    before=len(calls());p=invoke(['build','main.soma'],ok)
    if hit is not None: assert ('reused checking/extraction' in p.stdout)==hit,(hit,p.stdout,p.stderr)
    assert len(calls())>before, 'native validation command was skipped'
    return p

def calls():
    path=work/'calls'
    return [json.loads(x) for x in path.read_text().splitlines() if json.loads(x)[:1]==['exec']] if path.exists() else []

def output():
    p=subprocess.run([str(app/'main.exe')],cwd=app,env=env,text=True,capture_output=True,timeout=10)
    assert p.returncode==0,p.stderr
    return p.stdout

def plans(): return sorted((work/'cache'/'soma-native-phases').glob('*'))
def latest(): return max(plans(),key=lambda x:x.stat().st_mtime_ns)

build(False); assert '1 42' in output()
assert plans(), 'compiler did not certify a supported native checking/extraction phase'
build(True); assert calls()[-1][-7:]==['dune','build','--profile','release','--root','.','./soma_main.exe']
assert '1 42' in output()
# Native products are not freshness proofs; missing/tampered outputs are
# repaired through an actual Dune run and a producer-checked copy.
(app/'main.exe').unlink();build(True);assert '1 42' in output()
(app/'main.exe').write_bytes(b'tampered product');build(True);assert '1 42' in output()
invoke(['build','--check-fresh','main.soma'],False)
# Corrupt copied plan metadata cannot create provenance.
p=latest();p.write_bytes(p.read_bytes()+b'forged\0');build(False);build(True)
# A modified generated input cannot become a producer-certified extraction.
project=next((work/'cache'/'soma'/'ocaml'/'build').glob('main-*'))
(project/'prog.ml').write_text('let forged = 1\n');build(False);build(True)
(project/'.soma-ocaml-files').write_text('forged ownership\n');build(False);build(True)
# Root, companion expectations, automatic extension, and foreign source drift.
source.write_text(original+'\n(* source change *)\n');build(False);build(True)
exp=app/'main.exp';exp.write_text('Lemma phase_property : True.\nProof. exact I. Qed.\n');build(False);build(False)
exp.write_text('Lemma bad_property : False.\nProof. exact I. Qed.\n');invoke(['build','main.soma'],False)
exp.unlink();build(True)
ext=app/'main.ext';ext.write_text('(* extension source *)\n');build(False);build(False)
ext.unlink();build(True)
rules=app/'native_phase_probe.ext';rules.write_text('(* folder rules *)\n');build(False)
rules.write_text('(* changed folder rules *)\n');build(False);rules.unlink();build(True)
# Even benign launch-environment/unsupported argument changes cannot hit a
# certificate for a different semantic request.
env['PHASE_PROBE_UNKNOWN_OPTION']='changed';build(False);env.pop('PHASE_PROBE_UNKNOWN_OPTION');build(True)
p=invoke(['build','main.soma','-w','-all']);assert 'reused checking/extraction' not in p.stdout
foreign.write_text('let succ (n : Soma_nat.nat) : Soma_nat.nat = n + 2\n');build(False);assert '2 43' in output();build(True)
# Source Load is deliberately unsupported, including inputs outside the root.
outside=work/'outside.v';outside.write_text('Definition loaded_number := 7.\n')
source.write_text('Load "'+str(outside)+'".\n'+original);build(False);build(False)
outside.write_text('Definition loaded_number := 8.\n');build(False)
source.write_text(original);build(False);build(True)
# Default RC absence is itself an input, even without changing env/HOME.
rc=work/'config'/'coq'/'coqrc';rc.parent.mkdir(parents=True);rc.write_text('(* late startup file *)\n')
build(False);build(False);rc.unlink();build(True)
# A native validator failure never becomes success through an earlier plan.
(work/'fail').write_text('fail native validator');build(None,False);(work/'fail').unlink();build(True)
# Broken source cannot hide behind a previously successful phase.
source.write_text('Import succ.\nmain : nat := true.\n');invoke(['build','main.soma'],False)
source.write_text(original);build(True)
# Mutation after phase lookup but before Dune completes cannot certify a
# different source. Fallback must really check the changed, invalid root.
(work/'mutate').write_text(json.dumps({'path':str(source),'text':'Import succ.\nmain : nat := true.\n'}))
build(None,False)
source.write_text(original);build(True)
for row in measurements: print(json.dumps(row))
print('native phase reuse preserves Dune, input drift, provenance and failure validation: passed')
PY
