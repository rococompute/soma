#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?;if [ "$rc" != 0 ];then tail -n 60 "$WORK"/*.log 2>/dev/null||true;fi;rm -rf "$WORK"' EXIT
ocaml(){ opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }
mkdir "$WORK/app"
cp "$HERE"/examples/example_projects/native_constructor/* "$WORK/app/"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
python3 - "$WORK" <<'PY'
from pathlib import Path
import sys
w=Path(sys.argv[1]);abi=(w/'native/native_abi.manifest').read_text();binding=(w/'native/soma_bindings.ml').read_text()
assert 'constructor-tag' in abi and 'constructor-case' in abi
assert 'Obj.'not in binding
seen=set()
for line in(w/'hash').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split())
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PY
cat > "$WORK/native/probe.ml" <<'ML'
open Fixture
let ensure name value=if not value then failwith name
let ()=
 let a=Bytes.to_string(Bytes.make 1001 'a')and b=Bytes.to_string(Bytes.make 1009 'b')and c=Bytes.to_string(Bytes.make 1013 'c')in
 let table=Hashtbl.create 8in Hashtbl.add table "key" a;
 let values=[Empty;Name a;Pair(a,b);Triple(a,b,c);Inline{text=a};Directory table]in
 List.iter(fun value->
  ensure"empty tag"(Prog.empty_tag value=(match value with Empty->true|_->false));
  ensure"name tag"(Prog.name_tag value=(match value with Name _->true|_->false));
  ensure"pair tag"(Prog.pair_tag value=(match value with Pair _->true|_->false));
  ensure"inline record tag"(Prog.inline_tag value=(match value with Inline _->true|_->false));
  ensure"empty case"(Prog.empty_value value=(match value with Empty->Some()|_->None));
  ensure"name case"(match Prog.name_value value,value with Some payload,Name original->payload==original|None,Name _->false|None,_->true|_->false);
  ensure"pair case ordered aliases"(match Prog.pair_value value,value with Some(x,y),Pair(a,b)->x==a&&y==b|None,Pair _->false|None,_->true|_->false);
  ensure"triple case nested ordered aliases"(match Prog.triple_value value,value with Some(x,(y,z)),Triple(a,b,c)->x==a&&y==b&&z==c|None,Triple _->false|None,_->true|_->false);
  ensure"directory table alias"(match Prog.directory_value value,value with Some found,Directory original->found==original|None,Directory _->false|None,_->true|_->false)
 )values;
 ensure"global unqualified nullary constructor"(Prog.missing_tag Not_found&&not(Prog.missing_tag(Failure a)));
 ensure"qualified exception payload alias"(match Prog.failure_text(Failure a)with Some text->text==a|_->false);
 let payload=Option.get(Prog.name_value(Name a))in Bytes.set(Bytes.unsafe_of_string a)0 '?';ensure"mutable payload alias"(payload.[0]='?');
 let found=Option.get(Prog.directory_value(Directory table))in Hashtbl.replace found "key" b;ensure"mutable table alias"(Hashtbl.find table "key"==b);
 let consume project make=
  let weak=Weak.create 1in
  let[@inline never] call()=let owner=make()in Weak.set weak 0(Some owner);project owner in
  let result=call()in Gc.full_major();Gc.full_major();let kept=Weak.check weak 0in ignore(Sys.opaque_identity result);kept in
 ensure"consumed kind owner releases like direct match"(consume Prog.name_value(fun()->Name(String.make 4096 'x'))=consume(function Name name->Some name|_->None)(fun()->Name(String.make 4096 'x')));
 print_endline"PASS: named native constructors: nullary/unary/multiple/inline tags, optional borrowed payloads, ordered nested tuples, mutable aliases and consumed-owner Weak phases"
ML
python3 - "$WORK/native" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);f=p/'probe.ml';f.write_text(f.read_text().replace('8in','8 in').replace('1in','1 in').replace('0in','0 in'))
mods=sorted(f.stem for f in p.glob('*.ml')if f.stem!='soma_main')
(p/'dune').write_text('(executable (name probe) (modes exe byte) (modules '+' '.join(mods)+') (libraries lwt) (flags (:standard -w -a)))\n')
PY
ocaml dune build --root "$WORK/native" --profile release probe.exe probe.bc > "$WORK/build.log" 2>&1
ocaml "$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"

cp "$WORK/hash" "$WORK/before.hash"
python3 - "$WORK/app/fixture.definition" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);p.write_text(p.read_text().replace('bool := "Name" 1.','bool := "Directory" 1.'))
PY
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/after.hash"
if cmp -s "$WORK/before.hash" "$WORK/after.hash";then echo 'constructor target failed to change logical hash' >&2;exit 1;fi
negative(){
 local case_name=$1 declaration=$2 expected=$3 ffi=${4:-0}
 mkdir "$WORK/$case_name"
 cp "$HERE"/examples/example_projects/native_constructor/* "$WORK/$case_name/"
 printf 'From Soma Require Native.\nImport fixture.\n%s\n' "$declaration" > "$WORK/$case_name/bad.definition"
 printf 'From Soma Require Native.\nImport bad.\nDefinition main:=bad.\n' > "$WORK/$case_name/main.soma"
 if [ "$ffi" = 1 ];then
  "$SOMA" extract "$WORK/$case_name/main.soma" -o "$WORK/$case_name/native" > "$WORK/$case_name.log" 2>&1
  if ocaml dune build --root "$WORK/$case_name/native" --profile release >> "$WORK/$case_name.log" 2>&1;then echo "accepted $case_name" >&2;exit 1;fi
 else
  if "$SOMA" extract "$WORK/$case_name/main.soma" -o "$WORK/$case_name/native" > "$WORK/$case_name.log" 2>&1;then echo "accepted $case_name" >&2;exit 1;fi
 fi
 grep -q "$expected" "$WORK/$case_name.log"
}
negative nonnative_input 'OCaml Native Tag bad : string -> bool := "Name" 1.' 'declared native type'
negative wrong_tag_result 'OCaml Native Tag bad : kind -> string := "Name" 1.' 'Tag result must be bool'
negative wrong_case_result 'OCaml Native Case bad : kind -> string := "Name" 1.' 'Case result must be option'
negative wrong_nullary_payload 'OCaml Native Case bad : kind -> option string := "Empty" 0.' 'nullary Case payload must be unit'
negative malformed_ctor 'OCaml Native Case bad : kind -> option string := "Name;exit" 1.' 'uppercase OCaml'
negative lowercase_ctor 'OCaml Native Tag bad : kind -> bool := "name" 1.' 'uppercase OCaml'
negative wrong_arity 'OCaml Native Case bad : kind -> option (string*string) := "Name" 2.' 'Error:' 1
negative wrong_tag_arity 'OCaml Native Tag bad : kind -> bool := "Pair" 1.' 'Error:' 1
negative wrong_payload 'OCaml Native Case bad : kind -> option bool := "Name" 1.' 'Error:' 1
negative missing_ctor 'OCaml Native Tag bad : kind -> bool := "Does_not_exist" 0.' 'Error:' 1
negative inline_escape 'OCaml Native Case bad : kind -> option string := "Inline" 1.' 'Error:' 1
echo 'PASS: constructor target hashes and native input/result/path/nullary checks; actual ABI rejects wrong arities/payloads, missing constructors and escaping inline records'
if [ "${SOMA_TEST_HVF:-0}" = 1 ];then
 mkdir "$WORK/image"
 cp "$HERE"/examples/example_projects/native_constructor/fixture.* "$WORK/image/"
 printf '[project]\nname="native_constructor_image"\nversion="0.1.0"\n' > "$WORK/image/soma.toml"
 printf 'From Soma Require Native.\ninvoke : (unit -> Native.entry string) -> string.\n' > "$WORK/image/caller.definition"
 printf 'let invoke f = f ()\n' > "$WORK/image/caller.ml"
 cat > "$WORK/image/main.soma" <<'SOMA'
Require Import Sandbox.
From Soma Require Native.
Import fixture caller.
Definition probe:=Native.Export(Native.Bind(Native.Call_callback make tt)(fun value=>
 Native.Bind(Native.Call_callback name value)(fun result=>Native.Return(match result with Some text=>text|None=>"missing"end)))).
Definition main:io unit:=
 text<-call(fun _=>invoke(fun _=>probe));;
 if String.eqb text "native constructor"then print "native constructor bindings in Solo5 verified"else exit 1.
SOMA
 SOMA_MIRAGE_SWITCH=${SOMA_MIRAGE_SWITCH:-kykeon} SOMA_MIRAGE_DIR="$WORK/image-project" \
 SOMA_OCAML_BINDINGS_MODULE=Constructor_image_bindings "$SOMA" build "$WORK/image/main.soma" > "$WORK/image-build.log" 2>&1
 timeout 30 opam exec --switch="${SOMA_MIRAGE_SWITCH:-kykeon}" -- solo5-hvt --mem=256 -- "$WORK/image/main.hvt" > "$WORK/image-boot.log" 2>&1
 grep -q 'native constructor bindings in Solo5 verified' "$WORK/image-boot.log"
 echo 'PASS: typed native constructor projection executes inside actual Solo5'
fi
echo 'native constructor bindings: ok'
