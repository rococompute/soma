#!/usr/bin/env bash
# Closed native functions bind a checked required boolean label without captured adapters.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 45 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
let trace=ref[]
let context:string Lwt.key=Lwt.new_key()
let observe=ref(fun (_:string) (_:string)->())
let response=ref(Lwt.return "reply")
let flags:bool list ref=ref[]
let default()=trace:="default":: !trace;true
let invoke ?(enabled=default()) ~tail ~label text=
 trace:="invoke":: !trace;flags:=tail:: !flags;
 if not enabled then failwith "changed optional default";
 (!observe)label text;!response
let other=invoke
let pair_flags=ref(false,false)
let pair ~left ~right text=pair_flags:=left,right;text
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native Callable invocation Optional enabled := forall (enabled:option bool) (tail:bool) (label:string), string -> promise string.
OCaml Native External Bound Function head : string -> string -> promise string := "Target.invoke" Binding "tail" false Using invocation.
OCaml Native External Bound Function tail : string -> string -> promise string := "Target.invoke" Binding "tail" true Using invocation.
OCaml Native Callable pair_call := forall (left:bool) (right:bool), string -> string.
OCaml Native External Bound Function left : bool -> string -> string := "Target.pair" Binding "left" false Using pair_call.
OCaml Native External Bound Function right : bool -> string -> string := "Target.pair" Binding "right" false Using pair_call.
OCaml Native Callable optional_call Optional tail := forall (tail:option bool), string -> string.
OCaml Native Callable only_call := forall (tail:bool), string.
Fail OCaml Native External Bound Function absent : string -> string -> promise string := "Target.invoke" Binding "missing" false Using invocation.
Fail OCaml Native External Bound Function optional : string -> string := "Target.pair" Binding "tail" false Using optional_call.
Fail OCaml Native External Bound Function wrong_type : string -> bool -> promise string := "Target.invoke" Binding "tail" false Using invocation.
Fail OCaml Native External Bound Function wrong_result : string -> string -> string := "Target.invoke" Binding "tail" false Using invocation.
Fail OCaml Native External Bound Function missing_argument : string -> promise string := "Target.invoke" Binding "tail" false Using invocation.
Fail OCaml Native External Bound Function named : forall (label:string), string -> promise string := "Target.invoke" Binding "tail" false Using invocation.
Fail OCaml Native External Bound Function non_bool : string -> bool -> promise string := "Target.invoke" Binding "label" false Using invocation.
Fail OCaml Native External Bound Function no_required : string := "Target.invoke" Binding "tail" false Using only_call.
Fail OCaml Native External Bound Function injected : string -> string -> promise string := "Target.invoke; assert false" Binding "tail" false Using invocation.
Fail OCaml Native External Bound Function label_code : string -> string -> promise string := "Target.invoke" Binding "tail; assert false" false Using invocation.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target.
Definition head_factory := Native.Export (Native.Return head).
Definition tail_factory := Native.Export (Native.Return tail).
Definition left_factory := Native.Export (Native.Return left).
Definition right_factory := Native.Export (Native.Return right).
Definition main := (head_factory,tail_factory,left_factory,right_factory).
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
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml,target.ml} .
cp native/soma_callable_*.ml .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let original_head()=fun label text->Target.invoke ~tail:false ~label text
let original_tail()=fun label text->Target.invoke ~tail:true ~label text
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let head=Prog.head_factory()and tail=Prog.tail_factory()in
 require "closed callback sharing"((original_head()==original_head())=(head==Prog.head_factory())&&(original_tail()==original_tail())=(tail==Prog.tail_factory()));
 let label=String.make 1048576 'l'and text=String.make 1048576 't'in
 Target.observe:=(fun l t->require "native arguments borrowed"(l==label&&t==text);require "caller context"(Lwt.get Target.context=Some "caller"));
 let ready=Lwt.return "ready" and pending,wake=Lwt.task()and fault=Failure "bound boolean"in
 List.iter(fun(fn,flag)->Target.trace:=[];let partial=fn label in
  require "partial call does not invoke target/default"(!Target.trace=[]);
  List.iter(fun response->Target.response:=response;Target.trace:=[];Target.flags:=[];
   let result=Lwt.with_value Target.context(Some "caller")(fun()->partial text)in
   require "exact native returned promise"(result==response);
   require "bound flag and native default"(!Target.flags=[flag]&&List.rev !Target.trace=["default";"invoke"]))[ready;pending;Lwt.fail fault]) [head,false;tail,true];
 Target.response:=pending;let cancelled=ref 0 in Lwt.on_cancel pending(fun()->incr cancelled);
 let result=Lwt.with_value Target.context(Some "caller")(fun()->head label text)in Lwt.cancel result;
 require "native cancellation propagated"(!cancelled=1);ignore(Sys.opaque_identity wake);
 Target.observe:=(fun _ _->raise fault);
 require "exact synchronous exception"(try ignore(head label text);false with error->error==fault);
 Target.observe:=(fun _ _->());Target.response:=ready;
 let measure run=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do run()done;Gc.allocated_bytes()-.before in
 let a=measure(fun()->ignore(Sys.opaque_identity(original_head())))and b=measure(fun()->ignore(Sys.opaque_identity(Prog.head_factory())))in
 Printf.printf "bound closed creation allocation %.0f/%.0f B\n%!"a b;require "closed creation allocation parity"(a=b);
 let old=original_head()in
 let a=measure(fun()->ignore(Sys.opaque_identity(old label text)))and b=measure(fun()->ignore(Sys.opaque_identity(head label text)))in
 Printf.printf "bound invocation allocation %.0f/%.0f B\n%!"a b;require "no per-call argument/program bridge"(a=b);
 let phases fn=
  let weak=Weak.create 2 and seen=ref[]in
  Target.observe:=(fun _ _->collect();seen:=(Weak.check weak 0,Weak.check weak 1):: !seen);
  let[@inline never] invoke()=let label=String.make 1000000 'l'and text=String.make 1000000 't'in
   Weak.set weak 0(Some label);Weak.set weak 1(Some text);fn label text in
  let result=invoke()in collect();require "consumed arguments released after return"(not(Weak.check weak 0)&&not(Weak.check weak 1));
  Target.observe:=(fun _ _->());ignore(Sys.opaque_identity result);List.rev !seen in
 require "callback-time argument Weak phases"(phases old=phases head);
 let borrowed=String.make 2000000 'x'in
 require "bound first required label"(Prog.left_factory()true borrowed==borrowed&& !Target.pair_flags=(false,true));
 require "bound later required label"(Prog.right_factory()true borrowed==borrowed&& !Target.pair_flags=(true,false));
 print_endline "PASS: bound boolean functions preserve closed native/bytecode sharing, defaults/labels, partial/fault phases, borrowed arguments/promises, context/cancellation, exact allocations and Weak lifetimes."
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml soma_callable_*.ml target.ml soma_bindings.ml prog.mli prog.ml check.ml
 ./"check-$compiler"
done
# The target must match the entire native schema, including the bound label.
cp target.ml original-target.ml
sed 's/let invoke ?(enabled=default()) ~tail ~label text=/let invoke ?(enabled=default()) ~label text= let tail=false in/' original-target.ml >native/target.ml
if (cd native && dune build --profile release -j2)>bad-build.log 2>&1;then echo 'accepted missing required bound label' >&2;exit 1;fi
rg -q 'tail|Labels' bad-build.log
cp original-target.ml native/target.ml
cp target.definition original-target.definition
cp native/native_abi.manifest baseline-abi
cp hash.log baseline-hashes
# A bound value changes meaning even when every host type and symbol stays the same.
sed 's/Binding "tail" false Using invocation\./Binding "tail" true Using invocation./g' original-target.definition >target.definition
soma extract main.soma -no-soma-prelude -o changed-native >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hashes
if cmp -s baseline-abi changed-native/native_abi.manifest;then echo 'bound value absent from native ABI' >&2;exit 1;fi
python3 - <<'PY'
from pathlib import Path
def hashes(path):return {line.split()[2]:line.split()[:2]for line in Path(path).read_text().splitlines()if len(line.split())>=3}
a=hashes('baseline-hashes');b=hashes('changed-hashes')
for key in ('target.head','main.head_factory','main.main'):
 assert a[key][0]!=b[key][0] and a[key][1]!=b[key][1],(key,a[key],b[key])
PY
# Binding another same-typed label also changes semantic and ABI identities.
sed 's/Binding "left" false Using pair_call\./Binding "right" false Using pair_call./g' original-target.definition >target.definition
soma extract main.soma -no-soma-prelude -o relabelled-native >relabelled.log 2>&1
soma hash main.soma -no-soma-prelude >relabelled-hashes
if cmp -s baseline-abi relabelled-native/native_abi.manifest;then echo 'bound label absent from native ABI' >&2;exit 1;fi
python3 - <<'PY'
from pathlib import Path
def hashes(path):return {line.split()[2]:line.split()[:2]for line in Path(path).read_text().splitlines()if len(line.split())>=3}
a=hashes('baseline-hashes');b=hashes('relabelled-hashes')
for key in ('target.left','main.left_factory','main.main'):
 assert a[key][0]!=b[key][0] and a[key][1]!=b[key][1],(key,a[key],b[key])
PY
