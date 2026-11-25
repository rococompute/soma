#!/usr/bin/env bash
# Named checked callable adapters omit optional arguments and preserve closed callback phases.
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
let response=ref(Lwt.return "initial")
let default()=trace:="default" :: !trace;true
let invoke ?(enabled=default()) ~label text=
 trace:="invoke" :: !trace;
 if not enabled then failwith "changed optional default";
 (!observe)label text;!response
let other=invoke
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native Callable invocation Optional enabled := forall (enabled : option bool) (label : string), string -> promise string.
OCaml Native External Defaulted Function invoke : string -> string -> promise string := "Target.invoke" Using invocation.
Fail OCaml Native External Defaulted Function missing : string -> promise string := "Target.invoke" Using invocation.
Fail OCaml Native External Defaulted Function changed : string -> bool -> promise string := "Target.invoke" Using invocation.
Fail OCaml Native External Defaulted Function changed_result : string -> string -> bool := "Target.invoke" Using invocation.
Fail OCaml Native External Defaulted Function injection : string -> string -> promise string := "Target.invoke; failwith" Using invocation.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target.
Definition body := Native.Export (Native.Return invoke).
Definition main := body.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PYASSUMPTIONS'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes ' in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PYASSUMPTIONS
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml,target.ml} .
cp native/soma_callable_*.ml .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let original()=fun label text->Target.invoke ~label text
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let old=original()and current=Prog.body()in
 require "closed callback creation identity"((old==original())=(current==Prog.body()));
 let label=String.make 1000000 'l'and text=String.make 1000000 't'in
 Target.observe:=(fun l t->require "borrowed named arguments"(l==label&&t==text);require "invocation context"(Lwt.get Target.context=Some "caller"));
 Target.trace:=[];let partial=current label in require "partial call does not apply defaults"(!Target.trace=[]);
 let ready=Lwt.return text and pending,wake=Lwt.task()and fault=Failure "named function"in let rejected=Lwt.fail fault in
 List.iter(fun response->Target.response:=response;Target.trace:=[];
  let result=Lwt.with_value Target.context(Some "caller")(fun()->partial text)in
  require "exact returned native promise"(result==response);
  require "optional defaults and invocation stages"(List.rev !Target.trace=["default";"invoke"]))[ready;pending;rejected];
 let canceled=ref 0 in Lwt.on_cancel pending(fun()->incr canceled);Target.response:=pending;
 let result=Lwt.with_value Target.context(Some "caller")(fun()->current label text)in Lwt.cancel result;require "direct cancellation"(!canceled=1);ignore(Sys.opaque_identity wake);
 Target.observe:=(fun _ _->raise fault);
 require "exact synchronous callback fault"(try ignore(current label text);false with error->error==fault);
 Target.observe:=(fun _ _->());Target.response:=ready;Target.trace:=[];
 let measure run=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do run()done;Gc.allocated_bytes()-.before in
 let a=measure(fun()->ignore(Sys.opaque_identity(original())))and b=measure(fun()->ignore(Sys.opaque_identity(Prog.body())))in
 Printf.printf "closed defaulted function allocation %.0f/%.0f B\n%!"a b;require "original closed creation allocation"(a=b);
 let a=measure(fun()->ignore(Sys.opaque_identity(old label text)))and b=measure(fun()->ignore(Sys.opaque_identity(current label text)))in
 Printf.printf "defaulted invocation allocation %.0f/%.0f B\n%!"a b;require "no callable argument bridge allocation"(a=b);
 let phases run=
  let weak=Weak.create 2 and seen=ref[]in
  Target.trace:=[];Target.observe:=(fun _ _->collect();seen:=(Weak.check weak 0,Weak.check weak 1)::!seen);
  let[@inline never] invoke()=let label=String.make 1048576 'l'and text=String.make 1048576 't'in
   Weak.set weak 0(Some label);Weak.set weak 1(Some text);run label text in
  let result=invoke()in collect();require "consumed arguments released"(not(Weak.check weak 0)&&not(Weak.check weak 1));
  Target.observe:=(fun _ _->());ignore(Sys.opaque_identity result);List.rev !seen in
 require "callback-time Weak argument phases"(phases old=phases current);
 print_endline "PASS: named defaulted functions retain optional defaults, labels, closed sharing/creation, partial/fault phases, borrowed arguments/promises, context/cancellation, exact allocations and Weak phases."
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml soma_callable_*.ml target.ml soma_bindings.ml prog.mli prog.ml check.ml
 "./check-$compiler"
done
# The named implementation must retain the entire declared native schema.
cp target.ml original-target.ml
sed 's/let invoke ?(enabled=default()) ~label text=/let invoke ~label text= let enabled=true in/' target.ml > bad.ml
cp bad.ml target.ml
cp target.ml native/target.ml
if (cd native && dune build --profile release -j2)>bad-build.log 2>&1;then echo 'accepted incompatible native callable implementation' >&2;exit 1;fi
rg -q 'enabled|Labels' bad-build.log
# Restore the same implementation before comparing identities.
cp original-target.ml target.ml
# Only changing the selected native symbol invalidates both semantic and native ABI identities.
cp native/native_abi.manifest baseline-abi
cp hash.log baseline-hashes
sed -i.bak 's/:= "Target.invoke" Using/:= "Target.other" Using/g' target.definition
soma extract main.soma -no-soma-prelude -o changed-native >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hashes
if cmp -s baseline-abi changed-native/native_abi.manifest;then echo 'named symbol absent from native ABI' >&2;exit 1;fi
python3 - <<'PYHASH'
from pathlib import Path
def hashes(path):return {line.split()[2]:line.split()[:2] for line in Path(path).read_text().splitlines() if len(line.split())>=3}
a=hashes('baseline-hashes');b=hashes('changed-hashes')
for key in ('main.body','main.main','target.invoke'):
 assert a[key][0]!=b[key][0] and a[key][1]!=b[key][1],(key,a[key],b[key])
PYHASH
