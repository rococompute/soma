#!/usr/bin/env bash
# Closed native call and variant factories retain original preparation phases.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 50 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
let calls=ref 0
let observe=ref(fun (_:string)->())
let value=ref "result"
let result=ref(Lwt.return "result")
let text message=incr calls;(!observe)message;!value
let pending message=incr calls;(!observe)message;!result
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Thunk Factory invalid : unit -> unit -> PrimInt63.int := "Stdlib.invalid_arg" With "negative shell index".
OCaml Native External Thunk Factory failure : unit -> unit -> string := "Stdlib.failwith" With "fixed failure".
OCaml Native External Thunk Factory text : unit -> unit -> string := "Target.text" With "static literal".
OCaml Native External Thunk Factory pending : unit -> unit -> promise string := "Target.pending" With "static literal".
OCaml Native Polymorphic Variant token := ["N" : PrimInt63.int; "V" : string; "O" : string; "End"].
OCaml Native Construct Factory number : unit -> PrimInt63.int -> token := "N".
OCaml Native Construct Factory variable : unit -> string -> token := "V".
OCaml Native Construct Factory operator : unit -> string -> token := "O".
OCaml Native Construct Factory finish : unit -> unit -> token := "End".
OCaml Native Polymorphic Variant container (A : Type) := ["Payload" : A; "Empty"].
OCaml Native Construct Factory payload : forall (A : Type), unit -> A -> container A := "Payload".
Fail OCaml Native External Thunk Factory eager : unit -> string := "Target.text" With "literal".
Fail OCaml Native External Thunk Factory argument : unit -> string -> string := "Target.text" With "literal".
Fail OCaml Native External Thunk Factory wrong_factory : string -> unit -> string := "Target.text" With "literal".
Fail OCaml Native External Thunk Factory labelled : forall (arg : unit), unit -> string := "Target.text" With "literal".
Fail OCaml Native External Thunk Factory code : unit -> unit -> string := "Target.text; assert false" With "literal".
Fail OCaml Native Construct Factory missing_factory : PrimInt63.int -> token := "N".
Fail OCaml Native Construct Factory wrong_payload : unit -> string -> token := "N".
Fail OCaml Native Construct Factory absent : unit -> string -> token := "Unknown".
Fail OCaml Native Construct Factory wrong_nullary : unit -> string -> token := "End".
Fail OCaml Native Construct Factory wrong_answer : unit -> string -> string := "V".
Fail OCaml Native Construct Factory labelled_payload : unit -> forall (value : string), token := "V".
Fail OCaml Native Construct Factory injected : unit -> string -> token := "V; assert false".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
From Stdlib Require Import Strings.String.
Import target.
Definition invalid_factory := Native.Export (Native.Call_callback invalid tt).
Definition failure_factory := Native.Export (Native.Call_callback failure tt).
Definition text_factory := Native.Export (Native.Call_callback text tt).
Definition pending_factory := Native.Export (Native.Call_callback pending tt).
Definition number_factory := Native.Export (Native.Call_callback number tt).
Definition variable_factory := Native.Export (Native.Call_callback variable tt).
Definition operator_factory := Native.Export (Native.Call_callback operator tt).
Definition finish_factory := Native.Export (Native.Call_callback finish tt).
Definition payload_factory := Native.Export (Native.Call_callback (payload string) tt).
Definition callback_factory := Native.Export (Native.Call_callback (payload (string -> string)) tt).
Definition main := (invalid_factory,failure_factory,text_factory,pending_factory,
 number_factory,variable_factory,operator_factory,finish_factory,payload_factory,callback_factory).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes ' in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PY
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/{target.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_variant_*.ml .
# Use the authenticated program/bindings verbatim in one literal-pool unit.
{
 printf 'module Soma_bindings = struct\n'
 cat native/soma_bindings.ml
 printf '\nend\n'
 cat native/prog.ml
 cat <<'ML'
let require name value=if not value then failwith name
let original_invalid ()=fun ()->invalid_arg "negative shell index"
let original_failure ()=fun ()->failwith "fixed failure"
let original_text ()=fun ()->Target.text "static literal"
let original_pending ()=fun ()->Target.pending "static literal"
let original_number ()=fun value->`N value
let original_variable ()=fun value->`V value
let original_operator ()=fun value->`O value
let original_finish ()=fun ()->`End
let original_payload ()=fun value->`Payload value
let catch call=try ignore(call());failwith "expected failure"with error->error
let measure call=Gc.full_major();let before=Gc.allocated_bytes()in
 for _=1 to 100000 do call()done;Gc.allocated_bytes()-.before
let compare name original current=
 let a=measure original and b=measure current in
 require(name^" exact allocation")(a=b);Printf.printf "%s allocation %.0f/%.0f B\n"name a b
let sharing original current=
 let a=original()and b=original()and x=current()and y=current()in
 require "original native/bytecode factory sharing"((a==b)=(x==y));a,x
let ()=
 let old,new_=sharing original_invalid invalid_factory in
 let a=catch old and b=catch new_ in
 require "exact invalid argument"(a=Invalid_argument "negative shell index"&&a=b);
 require "fresh invalid argument identity parity"((a==catch old)=(b==catch new_));
 let old,new_=sharing original_failure failure_factory in
 require "exact failure"(catch old=Failure "fixed failure"&&catch new_=Failure "fixed failure");
 let old_text,new_text=sharing original_text text_factory in
 require "preparing native factories is quiet"(!Target.calls=0);
 let input=String.make 1048576 'r'in Target.value:=input;
 let key:string Lwt.key=Lwt.new_key()in
 Target.observe:=(fun literal->require "literal/caller context"(literal="static literal"&&Lwt.get key=Some "caller"));
 Lwt.with_value key(Some "caller")(fun()->require "direct result identity"(old_text()==input&&new_text()==input));
 let fault=Failure "exact leaf"in Target.observe:=(fun _->raise fault);
 require "native leaf failure identity"(catch old_text==fault&&catch new_text==fault);
 let old_pending,new_pending=sharing original_pending pending_factory in
 let promise,wake=Lwt.task()and canceled=ref 0 in Lwt.on_cancel promise(fun()->incr canceled);
 Target.result:=promise;Target.observe:=(fun _->require "pending caller context"(Lwt.get key=Some "caller"));
 Lwt.with_value key(Some "caller")(fun()->require "exact pending promise"(old_pending()==promise&&new_pending()==promise));
 Lwt.cancel promise;require "original cancellation"(!canceled=1);ignore(Sys.opaque_identity wake);
 let no,new_number=sharing original_number number_factory in
 List.iter(fun value->require "number tag/extreme payload"(no value=new_number value&&new_number value=`N value))[min_int;0;max_int];
 let vo,new_variable=sharing original_variable variable_factory in
 let oo,new_operator=sharing original_operator operator_factory in
 let eo,new_finish=sharing original_finish finish_factory in
 require "nullary variant"(eo()=new_finish()&&new_finish()=`End);
 let value=String.make 1048576 'p'in
 List.iter(fun constructor->require "variant borrows payload"(match constructor value with `V payload|`O payload->payload==value|_->false))
  [vo;new_variable;oo;new_operator];
 let po,new_payload=sharing original_payload payload_factory in
 require "generic variant payload identity"(match po value,new_payload value with `Payload a,`Payload b->a==value&&b==value|_->false);
 let callback=fun text->text in
 let callback_variant=callback_factory()callback in
 require "function payload borrowed without invocation"(match callback_variant with `Payload f->f==callback|_->false);
 let weak=Weak.create 1 in
 let retained=ref None in
 let prepare()=let value=String.make 1048576 'w'in Weak.set weak 0(Some value);retained:=Some(new_payload value)in
 prepare();Gc.full_major();Gc.full_major();require "returned variant owns payload"(Weak.check weak 0);
 ignore(Sys.opaque_identity !retained);retained:=None;Gc.full_major();Gc.full_major();require "factory releases consumed payload"(not(Weak.check weak 0));
 Target.observe:=(fun _->());
 compare "thunk factory"(fun()->ignore(Sys.opaque_identity(original_text())))(fun()->ignore(Sys.opaque_identity(text_factory())));
 compare "variant factory"(fun()->ignore(Sys.opaque_identity(original_variable())))(fun()->ignore(Sys.opaque_identity(variable_factory())));
 let old_invalid=original_invalid()and new_invalid=invalid_factory()in
 compare "invalid failure"(fun()->ignore(Sys.opaque_identity(catch old_invalid)))(fun()->ignore(Sys.opaque_identity(catch new_invalid)));
 compare "native invocation"(fun()->ignore(Sys.opaque_identity(old_text())))(fun()->ignore(Sys.opaque_identity(new_text())));
 compare "variant construction"(fun()->ignore(Sys.opaque_identity(vo value)))(fun()->ignore(Sys.opaque_identity(new_variable value)));
 print_endline "PASS: closed native/variant factories preserve original creation phases, aliases, borrowed and function payloads, ownership, literal calls, exact failures/promises/context/cancellation and allocation."
ML
} > check.ml
for compiler in ocamlc ocamlopt; do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml \
  soma_variant_*.ml target.ml check.ml
 "./check-$compiler"
done
# Native-call data/tag changes must invalidate both semantic and ABI identities.
python3 - <<'PY'
from pathlib import Path
p=Path('target.definition');p.write_text(p.read_text().replace('"negative shell index"','"changed index message"'))
PY
soma extract main.soma -no-soma-prelude -o native-changed >changed-extract.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
python3 - <<'PY'
from pathlib import Path
assert Path('hash.log').read_bytes()!=Path('changed-hash.log').read_bytes()
assert Path('native/native_abi.manifest').read_bytes()!=Path('native-changed/native_abi.manifest').read_bytes()
PY
printf 'PASS: closed factory literal changes invalidate native ABI and semantic hashes.\n'
python3 - <<'PY'
from pathlib import Path
p=Path('target.definition');p.write_text(p.read_text().replace('variable : unit -> string -> token := "V".','variable : unit -> string -> token := "O".'))
PY
soma extract main.soma -no-soma-prelude -o native-retagged >retagged-extract.log 2>&1
soma hash main.soma -no-soma-prelude >retagged-hash.log
python3 - <<'PY'
from pathlib import Path
assert Path('changed-hash.log').read_bytes()!=Path('retagged-hash.log').read_bytes()
assert Path('native-changed/native_abi.manifest').read_bytes()!=Path('native-retagged/native_abi.manifest').read_bytes()
PY
printf 'PASS: constructor factory tag changes invalidate native ABI and semantic hashes.\n'
# A descriptor's universal answer cannot disguise a less general host function.
mkdir wrong
cp target.ml wrong/target.ml
cat > wrong/target.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native External Thunk Factory wrong : forall (A : Type), unit -> unit -> A := "Target.text" With "literal".
SOMA
cat > wrong/main.soma <<'SOMA'
From Soma Require Import Native.
From Stdlib Require Import Strings.String.
Import target.
Definition main := Native.Export (Native.Call_callback (wrong string) tt).
SOMA
(cd wrong && soma extract main.soma -no-soma-prelude -o native) >wrong-extract.log 2>&1
if (cd wrong/native && dune build --profile release -j2) >wrong-build.log 2>&1; then
 printf 'less general native thunk implementation unexpectedly typechecked\n' >&2
 exit 1
fi
python3 - <<'PY'
from pathlib import Path
log=Path('wrong-build.log').read_text()
assert 'Error' in log and 'string' in log and 'Unbound module' not in log,log
PY
printf 'PASS: native thunk bindings reject less general host implementations.\n'
