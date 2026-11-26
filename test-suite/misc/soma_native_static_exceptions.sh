#!/usr/bin/env bash
# Public exception slots and their constructor/case rebasing belong to Source.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.."&&pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?;if [ "$rc" -ne 0 ];then tail -n 35 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type owner={bytes:bytes}
let boots:exn list ref=ref []
let boot error=boots:=error:: !boots;17
let weak:owner Weak.t=Weak.create 1
let[@inline never] fresh()=let value={bytes=Bytes.make 1048576 'x'}in Weak.set weak 0(Some value);value
ML
cat >slots.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "Target.owner".
OCaml Native Constructor failed : string -> exception_value := "Failed" 1.
OCaml Native Case failure_message : exception_value -> option string := "Failed" 1.
OCaml Native Constructor quit : unit -> exception_value := "Quit" 0.
OCaml Native Case quit_payload : exception_value -> option unit := "Quit" 0.
OCaml Native Constructor detailed : string -> owner -> exception_value := "Detailed" 2.
OCaml Native Case detail_payload : exception_value -> option (string * owner) := "Detailed" 2.
OCaml Native External Callback boot : exception_value -> PrimInt63.int := "Target.boot".
OCaml Native External Callback raise_slot : forall A : Type, exception_value -> A := "Stdlib.raise".
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
From Stdlib Require Import Strings.String.
Import slots.
Local Open Scope string_scope.
Definition prepared := Native.Export (Native.Bind (Native.Call_callback failed "initial")
 (fun error => Native.Call_callback boot error)).
Definition fail{A:Type} message := Native.Export (Native.Bind (Native.Call_callback failed message)
 (fun error => Native.Call_callback (raise_slot A) error)).
Definition inspect error := Native.Export (Native.Call_callback failure_message error).
Definition make_quit(_ : unit) := Native.Export (Native.Call_callback quit tt).
Definition inspect_quit error := Native.Export (Native.Call_callback quit_payload error).
Definition make_detail owner message := Native.Export (Native.Call_callback detailed (message,owner)).
Definition inspect_detail error := Native.Export (Native.Call_callback detail_payload error).
Definition unused := true.
Definition main := (prepared,(@fail,(inspect,(make_quit,(inspect_quit,(make_detail,inspect_detail)))))).
Fail OCaml Native Static Assembly main As "Checked" With [Exception "Other" := failed].
Fail OCaml Native Static Assembly main As "Checked" With [Exception "Failed" := failed;Exception "Failed" := failed].
Fail OCaml Native Static Assembly main As "Checked" With [Exception "Failed;bad" := failed].
Fail OCaml Native Static Assembly main As "Checked" With [Exception "Failed" := failure_message].
Fail OCaml Native Static Assembly main As "Checked" With [Exception "Unused" := unused].
OCaml Native Static Assembly main As "Checked" With [Exception "Failed" := failed;Exception "Quit" := quit;
 Exception "Detailed" := detailed;Value "prepared" := prepared;Value "fail" := fail;Value "inspect" := inspect;
 Value "make_quit" := make_quit;Value "inspect_quit" := inspect_quit;
 Value "make_detail" := make_detail;Value "inspect_detail" := inspect_detail].
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
rows=Path('native/native_assemblies.manifest').read_text().splitlines()
assert rows[0]=='soma-native-assemblies-v1' and len(rows)==2
symbol,source,src_hash,name,digest,program,interface,bindings,layout,contract=shlex.split(rows[1])
for path,expected in [(source,src_hash),('native/'+name,digest),('native/prog.ml',program),('native/prog.mli',interface),('native/soma_bindings.ml',bindings)]:
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==expected,path
assert next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]==symbol)==contract
abi=[shlex.split(l)for l in Path('native/native_abi.manifest').read_text().splitlines()[1:]]
identity=next(i for s,_,h,i in abi if s==symbol and h==src_hash).replace('\\n','\n')
assert 'static-exceptions-v1' in identity
assert hashlib.sha256(identity.encode()).hexdigest()==layout
for line in Path('hash.log').read_text().splitlines():
 assumptions=set(line.split('  assumes ',1)[1].split(', '))if'  assumes 'in line else set()
 assert assumptions<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},assumptions
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cp native/main.assembly one.ml
cp native/main.assembly two.ml
cat >check.ml <<'ML'
let require name value=if not value then failwith name
let ()=
 require "preparation count" (List.length !Target.boots=2);
 require "public slot before Checked initialization" (List.exists(function One.Failed "initial"->true|_->false)!Target.boots &&
  List.exists(function Two.Failed "initial"->true|_->false)!Target.boots);
 require "root slot name" (Printexc.exn_slot_name(One.Failed "a")="One.Failed");
 let first=One.Failed "message" in
 require "constructor/case rebasing" (One.inspect first=Some "message" && Two.inspect first=None);
 require "distinct zero-payload slots" (One.make_quit()==One.Quit && Two.inspect_quit One.Quit=None);
 let caught = try ignore(One.fail "first":int);assert false with One.Failed message->message in
 require "generic raised integer" (caught="first");
 let caught = try ignore(One.fail "second":string);assert false with One.Failed message->message in
 require "generic raised string" (caught="second");
 let kept=ref None in
 let[@inline never] construct()=
  let owner=Target.fresh()in
  let error=One.make_detail owner "detail"in
  (match One.inspect_detail error with Some(message,actual)->require "payload identity" (message="detail" && actual==owner)|_->assert false);
  require "cross-scope case" (Two.inspect_detail error=None);kept:=Some error
 in
 let[@inline never] use_kept()=match !kept with
  |Some error->(match One.inspect_detail error with
    |Some(message,owner)->require "retained payload remains usable" (message="detail" && Bytes.length owner.Target.bytes=1048576)
    |None->assert false)
  |None->assert false in
 construct();Gc.full_major();Gc.full_major();require "live exception owns original payload" (Weak.check Target.weak 0);
 use_kept();kept:=None;Gc.full_major();Gc.full_major();require "dropped exception releases payload naturally" (not(Weak.check Target.weak 0));
 print_endline "PASS: fresh root exception slots, initialization order, nullary/multiple payloads, generic raises, exact objects and natural Weak lifetime"
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt.unix -linkpkg -w -a uint63.ml soma_nat.ml soma_word64.ml soma_handles.ml soma_effect.ml float64.ml target.ml one.ml two.ml check.ml -o check >"$compiler.log" 2>&1
 ./check
done
# Reject generic payloads instead of emitting an unbound type variable.
cat >poly_slots.definition <<'SOMA'
From Soma Require Import Native Handles.
OCaml Native Constructor poly : forall A:Type,A -> exception_value := "Poly" 1.
SOMA
cat >poly.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import poly_slots.
Definition main := @poly.
Fail OCaml Native Static Assembly main As "Checked" With [Exception "Poly" := poly].
SOMA
soma hash poly.soma -no-soma-prelude >poly.log 2>&1
# Nested polymorphism must not introduce a free OCaml type variable either.
cat >higher_slots.definition <<'SOMA'
From Soma Require Import Native Handles.
OCaml Native Constructor higher : (forall A:Type,A -> A) -> exception_value := "Higher" 1.
SOMA
cat >higher.soma <<'SOMA'
From Soma Require Import Native OCaml.
Import higher_slots.
Definition main := higher.
Fail OCaml Native Static Assembly main As "Checked" With [Exception "Higher" := higher].
SOMA
soma hash higher.soma -no-soma-prelude >higher.log 2>&1
# Exception metadata is part of main's checked semantic identity.
cp hash.log before.log
sed -i.bak 's/Exception "Quit" := quit;//' main.soma
soma hash main.soma -no-soma-prelude >after.log
python3 - <<'PY'
from pathlib import Path
def main(file):return next(l.split()[0]for l in Path(file).read_text().splitlines()if l.split()[2]=='main.main')
assert main('before.log')!=main('after.log')
PY
cat >main.soma <<'SOMA'
Definition main := true.
SOMA
soma extract main.soma -no-soma-prelude -o native >plain.log 2>&1
test ! -e native/main.assembly
test ! -e native/native_assemblies.manifest
printf 'PASS: scoped exception validation, semantic identity, provenance and cleanup\n'
