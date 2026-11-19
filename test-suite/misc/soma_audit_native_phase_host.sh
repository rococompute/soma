#!/usr/bin/env bash
# Built-in Host depends on compiler-bundled Unix, not an external opam package.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
export SOMA_TEST_PHASE_HOST_WORK="$WORK"
python3 - <<'PY'
from pathlib import Path
import json,os,shutil,subprocess,time
work=Path(os.environ['SOMA_TEST_PHASE_HOST_WORK']).resolve();app=work/'app';app.mkdir()
(app/'soma.toml').write_text('[project]\nname="native_host_phase"\nversion="0.1.0"\n')
(app/'main.soma').write_text('Require Soma.Host.\nmain := Host.print_lines ["host-phase"].\n')
env=dict(os.environ,SOMA_OCAML_SWITCH=os.environ.get('SOMA_OCAML_SWITCH',str(Path.home()/'.cache/soma/ocaml')),XDG_CACHE_HOME=str(work/'cache'),XDG_CONFIG_HOME=str(work/'config'),SOMA_CACHE=str(work/'shared'))
compiler=shutil.which('soma');assert compiler

def build(hit):
 start=time.monotonic();p=subprocess.run([compiler,'build','main.soma'],cwd=app,env=env,text=True,capture_output=True,timeout=180)
 print(json.dumps(dict(seconds=time.monotonic()-start,exit=p.returncode,stdout=p.stdout,stderr=p.stderr)),flush=True)
 assert p.returncode==0,(p.stdout,p.stderr)
 assert ('reused checking/extraction' in p.stdout)==hit,(p.stdout,p.stderr)
 p=subprocess.run([str(app/'main.exe')],cwd=app,env=env,text=True,capture_output=True,timeout=10)
 assert p.returncode==0 and p.stdout=='host-phase\n',(p.stdout,p.stderr)
 assert (app/'main.exe').stat().st_mode & 0o777 == 0o755

build(False)
plans=list((work/'cache'/'soma-native-phases').glob('*'));assert plans,'Host+compiler Unix did not earn a phase plan'
project=next((work/'cache'/'soma'/'ocaml'/'build').glob('main-*'));assert (project/'soma_host_io.c').is_file()
before=(project/'build.log').stat().st_mtime_ns;build(True);assert (project/'build.log').stat().st_mtime_ns!=before
# Host C stubs are part of the producer-generated closure, not invisible SDK
# inputs: editing them must force fresh extraction before Dune and output copy.
(project/'soma_host_io.c').write_text('not generated Host code\n');build(False);build(True)
print('built-in Host/Unix phase reuse and C-stub invalidation: passed')
PY
