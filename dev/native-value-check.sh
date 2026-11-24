#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?;if [ "$rc" != 0 ];then tail -n 60 "$WORK"/*.log 2>/dev/null||true;fi;rm -rf "$WORK"' EXIT
ocaml(){ opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }
mkdir "$WORK/app"
cp "$HERE"/examples/example_projects/native_values/* "$WORK/app/"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
python3 - "$WORK" <<'PY'
from pathlib import Path
import sys
w=Path(sys.argv[1]);abi=(w/'native/native_abi.manifest').read_text();bindings=(w/'native/soma_bindings.ml').read_text()
assert 'external-value' in abi and 'Fixture.now' in abi and 'Sys.argv' in abi
assert 'Obj.'not in bindings
seen=set()
for line in(w/'hash').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int','Corelib.Floats.PrimFloat.float'},seen
PY
cat > "$WORK/native/probe.ml" <<'ML'
let ensure name value=if not value then failwith name
let ()=
 ensure"named array value borrowed"(Prog.arguments()==Sys.argv);
 ensure"named reference value borrowed"(Prog.cell()==Fixture.calls);
 ensure"function value read does not invoke"(Prog.function_value()==Fixture.compute&& !(Fixture.calls)=0);
 ensure"function value invoked explicitly"(Prog.call_function()=1&& !(Fixture.calls)=1);
 let key=Lwt.new_key()and trace=ref[]in
 Fixture.now:=(fun()->trace:=Lwt.get key::!trace;23.);
 ensure"clock cell read/call"(Lwt.with_value key(Some 17)Prog.clock=23.&& !trace=[Some 17]);
 Fixture.now:=(fun()->31.);ensure"clock sees replaced callback"(Prog.clock()=31.);
 let error=Failure"clock"in Fixture.now:=(fun()->raise error);
 ensure"clock exact synchronous error"(try ignore(Prog.clock());false with e->e==error);
 print_endline"PASS: named native values preserve array/reference/function identity, deferred invocation, replaced callbacks, dynamic context and exact synchronous exceptions"
ML
python3 - "$WORK/native" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);mods=sorted(f.stem for f in p.glob('*.ml')if f.stem!='soma_main')
(p/'dune').write_text('(executable (name probe) (modes exe byte) (modules '+' '.join(mods)+') (libraries lwt) (flags (:standard -w -a)))\n')
PY
ocaml dune build --root "$WORK/native" --profile release probe.exe probe.bc > "$WORK/build.log" 2>&1
ocaml "$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"

"$SOMA" hash "$WORK/app/main.soma" > "$WORK/before.hash"
python3 - "$WORK/app/fixture.definition" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);p.write_text(p.read_text().replace('"Sys.argv"','"Sys.executable_name"'))
PY
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/after.hash"
if cmp -s "$WORK/before.hash" "$WORK/after.hash";then echo 'named value target failed to change identity' >&2;exit 1;fi
negative(){
 local case_name=$1 declaration=$2 pattern=$3 ffi=${4:-0}
 mkdir "$WORK/$case_name"
 printf 'From Soma Require Native.\n%s\n' "$declaration" > "$WORK/$case_name/bad.definition"
 printf 'From Soma Require Native.\nImport bad.\nDefinition main:=bad.\n' > "$WORK/$case_name/main.soma"
 if [ "$ffi" = 1 ];then
  "$SOMA" extract "$WORK/$case_name/main.soma" -o "$WORK/$case_name/native" > "$WORK/$case_name.log" 2>&1
  if ocaml dune build --root "$WORK/$case_name/native" --profile release >> "$WORK/$case_name.log" 2>&1;then echo "accepted $case_name" >&2;exit 1;fi
 else
  if "$SOMA" extract "$WORK/$case_name/main.soma" -o "$WORK/$case_name/native" > "$WORK/$case_name.log" 2>&1;then echo "accepted $case_name" >&2;exit 1;fi
 fi
 grep -q "$pattern" "$WORK/$case_name.log"
}
negative malformed_path 'OCaml Native External Value bad : string := "Sys.executable_name;exit".' 'invalid value name'
negative invalid_module 'OCaml Native External Value bad : string := "sys.executable_name".' 'invalid module name'
negative wrong_type 'OCaml Native External Value bad : string := "Sys.argv".' 'Error:' 1
negative missing_value 'OCaml Native External Value bad : string := "Sys.no_such_value".' 'Error:' 1
negative accidental_call 'OCaml Native External Value bad : nat := "String.length".' 'Error:' 1
echo 'PASS: named value identities are hashed; malformed paths, wrong actual types, missing values and accidental function applications rejected'
if [ "${SOMA_TEST_HVF:-0}" = 1 ];then
 mkdir "$WORK/image"
 cp "$HERE"/examples/example_projects/native_values/fixture.* "$WORK/image/"
 printf '[project]\nname="native_values_image"\nversion="0.1.0"\n' > "$WORK/image/soma.toml"
 printf 'From Soma Require Native.\ninvoke : (unit -> Native.entry string) -> string.\n' > "$WORK/image/caller.definition"
 printf 'let invoke f = f ()\n' > "$WORK/image/caller.ml"
 cat > "$WORK/image/main.soma" <<'SOMA'
Require Import Sandbox.
From Soma Require Native.
From Corelib Require Import PrimFloat.
Import fixture caller.
Definition probe:=Native.Export(Native.Bind(Native.Call_callback clock_cell tt)(fun cell=>
 Native.Bind(Native.Read_reference cell)(fun current=>Native.Bind(Native.Call_callback current tt)(fun value=>
 Native.Return(if PrimFloat.eqb value 17%float then "late native clock"else "missing"))))).
Definition main:io unit:=
 text<-call(fun _=>invoke(fun _=>probe));;
 if String.eqb text "late native clock"then print "named native values in Solo5 verified"else exit 1.
SOMA
 SOMA_MIRAGE_SWITCH=${SOMA_MIRAGE_SWITCH:-kykeon} SOMA_MIRAGE_DIR="$WORK/image-project" \
 SOMA_OCAML_BINDINGS_MODULE=Value_image_bindings "$SOMA" build "$WORK/image/main.soma" > "$WORK/image-build.log" 2>&1
 timeout 30 opam exec --switch="${SOMA_MIRAGE_SWITCH:-kykeon}" -- solo5-hvt --mem=256 -- "$WORK/image/main.hvt" > "$WORK/image-boot.log" 2>&1
 grep -q 'named native values in Solo5 verified' "$WORK/image-boot.log"
 echo 'PASS: named native reference and function values execute inside actual Solo5'
fi
echo 'native named values: ok'
