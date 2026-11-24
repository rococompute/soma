#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?;if [ "$rc" != 0 ];then tail -n 60 "$WORK"/*.log 2>/dev/null||true;fi;rm -rf "$WORK"' EXIT
ocaml(){ opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }
mkdir "$WORK/app"
cp "$HERE"/examples/example_projects/native_external/* "$WORK/app/"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
python3 - "$WORK" <<'PY'
from pathlib import Path
import sys
w=Path(sys.argv[1]);abi=(w/'native/native_abi.manifest').read_text();out=w/'native'
assert 'external-call' in abi and 'Buffer.create' in abi and 'Buffer.t' in abi
assert not(out/'api.ml').exists()
assert 'Api.Buffer' not in(out/'soma_bindings.ml').read_text()
allowed={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'};seen=set()
for line in(w/'hash').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split())
assert seen==allowed,seen
PY
cat > "$WORK/native/probe.ml" <<'ML'
let ensure label value=if not value then failwith label
let ()=
 let payload=Bytes.to_string(Bytes.make 1024 'x')in
 ensure"borrowed external identity"(Prog.pass payload==payload);
 let buffer=Prog.make payload in
 ensure"absolute native type and functions"(Prog.read buffer=payload);
 Prog.append_text buffer "tail";ensure"native buffer alias"(Buffer.contents buffer=payload^"tail");
 let key=Lwt.new_key()in
 List.iter(fun mode->
  let pending,wake=Lwt.task()and error=Failure"external"in let events=ref[]in
  let next text=ensure"external bind payload alias"(text==payload);events:=(Lwt.get key)::!events;Lwt.return text in
  let raw=match mode with 0->Lwt.return payload|1->Lwt.fail error|_->pending in
  let result=Lwt.with_value key(Some 17)(fun()->Prog.then_text raw next)in
  Lwt.with_value key(Some 99)(fun()->match mode with 2->Lwt.wakeup wake payload|3->Lwt.wakeup_exn wake error|4->Lwt.cancel result|_->());
  (match mode,Lwt.state result with
   |(0|2),Lwt.Return text->ensure"external completion"(text==payload&& !events=[Some 17])
   |(1|3),Lwt.Fail exn->ensure"external exact failure"(exn==error&& !events=[])
   |4,Lwt.Fail Lwt.Canceled->ensure"external cancellation"(!events=[])
   |_->failwith"external promise phase")
 )[0;1;2;3;4];
 print_endline"PASS: external native types/functions need no forwarding module; buffer aliases, payload/exception identity, cancellation and scope preserved"
ML
python3 - "$WORK/native" <<'PY_DUNE'
from pathlib import Path
import sys
p=Path(sys.argv[1]);mods=sorted(f.stem for f in p.glob('*.ml')if f.stem!='soma_main')
(p/'dune').write_text('(executable (name probe) (modes exe byte) (modules '+' '.join(mods)+') (libraries lwt) (flags (:standard -w -a)))\n')
PY_DUNE
ocaml dune build --root "$WORK/native" --profile release probe.exe probe.bc > "$WORK/build.log" 2>&1
ocaml "$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"
# Absolute paths participate in hashes even when both targets have equal types.
cp "$WORK/hash" "$WORK/before.hash"
python3 - "$WORK/app/api.definition" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);p.write_text(p.read_text().replace('"Sys.opaque_identity"','"Fun.id"'))
PY
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/after.hash"
if cmp -s "$WORK/before.hash" "$WORK/after.hash";then echo 'external path failed to change logical hash' >&2;exit 1;fi
negative(){
 local case_name=$1 declaration=$2 pattern=$3
 mkdir "$WORK/$case_name"
 printf 'From Soma Require Native.\n%s\n' "$declaration" > "$WORK/$case_name/bad.definition"
 printf 'Import bad.\nDefinition main:=tt.\n' > "$WORK/$case_name/main.soma"
 if "$SOMA" extract "$WORK/$case_name/main.soma" -o "$WORK/$case_name/native" > "$WORK/$case_name.log" 2>&1;then echo "accepted $case_name" >&2;exit 1;fi
 grep -q "$pattern" "$WORK/$case_name.log"
}
negative invalid_type 'OCaml Native External Type bad := "Buffer.t;exit".' 'invalid value name'
negative invalid_module 'OCaml Native External Callback bad : string -> string := "sys.opaque_identity".' 'invalid module name'
negative invalid_symbol 'OCaml Native External Callback bad : string -> string := "Sys.opaque_identity;exit".' 'invalid value name'
negative nonfunction 'OCaml Native External Callback bad : string := "String.empty".' 'at least one argument'
ffi_negative(){
 local case_name=$1 declaration=$2
 mkdir "$WORK/$case_name"
 printf 'From Soma Require Native.\n%s\n' "$declaration" > "$WORK/$case_name/bad.definition"
 printf 'From Soma Require Native.\nImport bad.\nDefinition main:=bad.\n' > "$WORK/$case_name/main.soma"
 "$SOMA" extract "$WORK/$case_name/main.soma" -o "$WORK/$case_name/native" > "$WORK/$case_name.log" 2>&1
 if ocaml dune build --root "$WORK/$case_name/native" --profile release >> "$WORK/$case_name.log" 2>&1;then echo "accepted $case_name" >&2;exit 1;fi
 grep -q 'Error:' "$WORK/$case_name.log"
}
ffi_negative wrong_label 'OCaml Native External Callback bad : forall (value:string), string := "Sys.opaque_identity".'
ffi_negative wrong_type 'OCaml Native External Callback bad : string -> string := "String.length".'
ffi_negative missing_value 'OCaml Native External Callback bad : string -> string := "String.no_such_native_value".'
echo 'PASS: external path/signature identities are hashed; malformed paths and actual FFI type/label/missing-value errors are rejected'
if [ "${SOMA_TEST_HVF:-0}" = 1 ];then
 mkdir "$WORK/image"
 cp "$HERE/examples/example_projects/native_external/api.definition" "$WORK/image/"
 printf '[project]\nname="native_external_image"\nversion="0.1.0"\n' > "$WORK/image/soma.toml"
 printf 'From Soma Require Native.\ninvoke : (unit -> Native.entry string) -> string.\n' > "$WORK/image/caller.definition"
 printf 'let invoke f = f ()\n' > "$WORK/image/caller.ml"
 cat > "$WORK/image/main.soma" <<'SOMA'
Require Import Sandbox.
From Soma Require Native.
From Corelib Require Import PrimInt63.
Import api caller.
Definition probe:=Native.Export
 (Native.Bind(Native.Call_callback create 0%uint63)(fun buffer=>
 Native.Bind(Native.Call_callback append(buffer,"direct native buffer"))(fun _=>
 Native.Call_callback contents buffer))).
Definition main:io unit:=
 text<-call(fun _=>invoke(fun _=>probe));;
 if String.eqb text "direct native buffer"then print "external native bindings in Solo5 verified"else exit 1.
SOMA
 SOMA_MIRAGE_SWITCH=${SOMA_MIRAGE_SWITCH:-kykeon} SOMA_MIRAGE_DIR="$WORK/image-project" \
 SOMA_OCAML_BINDINGS_MODULE=External_image_bindings "$SOMA" build "$WORK/image/main.soma" > "$WORK/image-build.log" 2>&1
 timeout 30 opam exec --switch="${SOMA_MIRAGE_SWITCH:-kykeon}" -- solo5-hvt --mem=256 -- "$WORK/image/main.hvt" > "$WORK/image-boot.log" 2>&1
 grep -q 'external native bindings in Solo5 verified' "$WORK/image-boot.log"
 echo 'PASS: external native types and functions execute inside actual Solo5'
fi
echo 'external native bindings: ok'
