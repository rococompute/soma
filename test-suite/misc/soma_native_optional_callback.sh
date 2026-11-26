#!/usr/bin/env bash
# Optional callback inputs remain native options, with no option reconstruction.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ];then tail -n 28 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
type owner={ data:bytes; pending:bytes Lwt.t; mutable fault:exn option }
let key:int Lwt.key= Lwt.new_key()
let observe=ref(fun (_:owner) (_:bytes option) (_:bool) (_:bytes)->())
let slot:owner Weak.t=Weak.create 1
let forward owner ?choice ~enabled payload=
 (!observe) owner choice enabled payload;
 match owner.fault with Some error->raise error|None->owner.pending
let before owner choice ~enabled payload=forward owner ?choice ~enabled payload
let generic ?fallback value=match fallback with None->value|Some value->value
let generic_before fallback value=generic ?fallback value
let observe_many=ref(fun (_:bytes option) (_:bytes option)->())
let multiple ?first left ?last right=
 (!observe_many) first last;
 match first,last with Some value,_|_,Some value->value|_->if left==right then right else left
let consume owner ?choice payload=
 let result=Bytes.length owner.data+Bytes.length payload+(match choice with None->0|Some bytes->Bytes.length bytes) in
 Gc.full_major();result,Weak.check slot 0
let consume_before owner choice payload=consume owner ?choice payload
ML
cat >target.definition <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Type bytes := "Bytes.t".
OCaml Native External Type owner := "Target.owner".
OCaml Native External Callback forward Optional choice :
  owner -> forall (choice:option bytes) (enabled:bool), bytes -> promise bytes := "Target.forward".
OCaml Native External Callback generic Optional fallback :
  forall(A:Type)(fallback:option A), A -> A := "Target.generic".
OCaml Native External Callback consume Optional choice :
  owner -> forall(choice:option bytes), bytes -> (PrimInt63.int * bool) := "Target.consume".
OCaml Native External Callback multiple Optional last first :
  forall(first:option bytes),bytes -> forall(last:option bytes),bytes -> bytes := "Target.multiple".
OCaml Native External Callback before :
  owner -> option bytes -> forall (enabled:bool), bytes -> promise bytes := "Target.before".
OCaml Native External Callback generic_before :
  forall(A:Type),option A -> A -> A := "Target.generic_before".
OCaml Native External Callback consume_before :
  owner -> option bytes -> bytes -> (PrimInt63.int * bool) := "Target.consume_before".
Fail OCaml Native External Callback absent Optional missing : bytes -> bytes := "Target.generic".
Fail OCaml Native External Callback wrong Optional choice : forall(choice:bytes),bytes -> bytes := "Target.generic".
Fail OCaml Native External Callback twice Optional choice choice : forall(choice:option bytes),bytes -> bytes := "Target.generic".
Fail OCaml Native External Callback ambiguous Optional choice : forall(choice:option bytes)(choice:option bytes),bytes -> bytes := "Target.generic".
Fail OCaml Native External Callback type_parameter Optional A : forall(A:Type),A -> A := "Target.generic".
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native.
Import target.
Definition run owner choice enabled payload := Native.Export
 (Native.Call_callback forward (owner,(choice,(enabled,payload)))).
Definition generic_run {A:Type} choice (value:A) := Native.Export
 (Native.Call_callback (generic A) (choice,value)).
Definition consume_run owner choice payload := Native.Export
 (Native.Call_callback consume (owner,(choice,payload))).
Definition multiple_run first left last right := Native.Export
 (Native.Call_callback multiple (first,(left,(last,right)))).
Definition prior_run owner choice enabled payload := Native.Export
 (Native.Call_callback before (owner,(choice,(enabled,payload)))).
Definition prior_generic {A:Type} choice (value:A) := Native.Export
 (Native.Call_callback (generic_before A) (choice,value)).
Definition prior_consume owner choice payload := Native.Export
 (Native.Call_callback consume_before (owner,(choice,payload))).
Definition main(A:Type) := (run,generic_run(A:=A),consume_run,multiple_run,prior_run,prior_generic(A:=A),prior_consume).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'CHECK'
from pathlib import Path
seen=set()
for row in Path('hash.log').read_text().splitlines():
 if '  assumes 'in row:seen.update(row.split('  assumes ',1)[1].split(', '))
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
text=Path('native/soma_bindings.ml').read_text()
assert 'Target.forward a0 ?choice:a1 ~enabled:a2 a3' in text,text
assert '?fallback:a0' in text,text
CHECK
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cat >check.ml <<'ML'
let require name test=if not test then failwith name
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let data=Bytes.make 1048576 'o' and payload=Bytes.make 1048576 'p' in
 let pending,resolver=Lwt.task() in
 let owner={Target.data;pending;fault=None} in
 let choice=Some data in
 let calls=ref 0 in
 Target.observe:=(fun given_owner given enabled value->incr calls;
  require "original owner object"(given_owner==owner);
  require "original option box, content and payload"(given==choice && enabled && value==payload);
  require "caller context"(Lwt.get Target.key=Some 41));
 Lwt.with_value Target.key(Some 41)(fun()->
  let partial=Prog.run owner choice true in
  require "partial application runs no native effect"(!calls=0);
  require "exact original promise"(partial payload==pending && !calls=1);
  let fault=Failure "optional callback" in owner.fault<-Some fault;
  require "synchronous fault identity"(try ignore(Prog.run owner choice true payload);false with error->error==fault);
  owner.fault<-None);
 Target.observe:=(fun _ given _ value->require "None forwarded without Some"(given=None && value==payload));
 require "omitted option"(Prog.run owner None false payload==pending);
 Target.observe:=(fun _ _ _ _->());
 Lwt.wakeup_later resolver payload;
 require "resolution retains returned object"(Lwt_main.run pending==payload);
 let canceled,_=Lwt.task() in
 let other={owner with Target.pending=canceled}in
 require "cancelable promise borrowed"(Prog.run other None false payload==canceled);
 Lwt.cancel canceled;require "cancellation phase"(match Lwt.state canceled with Lwt.Fail Lwt.Canceled->true|_->false);
 require "generic default bytes"(Prog.generic_run None payload==payload);
 require "generic supplied bytes"(Prog.generic_run(Some data)payload==data);
 let closure()=data in require "generic closure"(Prog.generic_run(Some closure)(fun()->payload)==closure);
 let last=Some payload in
 Target.observe_many:=(fun first final->require "multiple option boxes/order"(first==choice && final==last));
 let partial=Prog.multiple_run choice data last in
 require "multiple optional arguments"(partial payload==data);
 let fault=Failure "multiple optional callback"in
 Target.observe_many:=(fun _ _->raise fault);
 require "multiple optional failure identity"(try ignore(partial payload);false with error->error==fault);
 Target.observe_many:=(fun _ _->());
 require "multiple omitted defaults"(Prog.multiple_run None data None payload==data);
 let measure fn=collect();let before=Gc.allocated_bytes()in
  for _=1 to 100000 do ignore(Sys.opaque_identity(fn owner choice true payload))done;
  Gc.allocated_bytes()-.before in
 let before=measure Prog.prior_run and after=measure Prog.run in
 Printf.printf "callback allocation %.0f/%.0f B\n%!"before after;
 require "exact per-call allocation"(before=after);
 let generic_measure fn=collect();let before=Gc.allocated_bytes()in
  for _=1 to 100000 do ignore(Sys.opaque_identity(fn choice payload))done;
  Gc.allocated_bytes()-.before in
 require "generic option forwarding allocation"(generic_measure Prog.prior_generic=generic_measure Prog.generic_run);
 Printf.printf "PASS: direct optional callbacks preserve option/owner/result identity, generic types, quiet partials, exact promises/context/faults/cancellation and allocation (%.0f/%.0f B).\n%!"before after
let lifetime call=
 let flags=ref[]in
 let invoke()=
  let payload=Bytes.make 4096 'p'in
  let owner={Target.data=Bytes.make 1048576 'o';pending=Lwt.return payload;fault=None}in
  Weak.set Target.slot 0(Some owner);
  let count,live=call owner None payload in flags:=[count,live]in
 invoke();collect();!flags,Weak.check Target.slot 0
let ()=
 let before=lifetime Prog.prior_consume and after=lifetime Prog.consume_run in
 require "consumed owner Weak phases"(before=after);
 require "natural owner release after return"(not(snd after));
 print_endline "PASS: optional callback consumed owners retain their native/bytecode Weak phases."
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt.unix -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_bindings.ml prog.mli prog.ml check.ml
 ./"check-$compiler"
done
cp target.definition saved-definition
cp native/native_abi.manifest saved-abi
# The checked option schema must still be checked against the actual OCaml ABI.
python3 - <<'MUTATE'
from pathlib import Path
p=Path('target.definition');s=p.read_text().replace('choice:option bytes) (enabled','choice:option string) (enabled',1);p.write_text(s)
MUTATE
soma extract main.soma -no-soma-prelude -o bad-native >bad-extract.log 2>&1
if (cd bad-native && dune build --profile release -j2)>bad-build.log 2>&1;then
 echo 'wrong actual optional ABI accepted' >&2;exit 1
fi
cp saved-definition target.definition
python3 - <<'MUTATE'
from pathlib import Path
p=Path('target.definition');s=p.read_text().replace('Callback forward Optional choice :','Callback forward :',1);p.write_text(s)
MUTATE
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash.log
if cmp -s hash.log changed-hash.log || cmp -s saved-abi changed/native_abi.manifest;then
 echo 'optional forwarding lost its semantic/ABI identity' >&2;exit 1
fi
printf '%s\n' 'PASS: optional callback shape/name/type/duplicate rejection, actual ABI rejection and semantic identity.'
