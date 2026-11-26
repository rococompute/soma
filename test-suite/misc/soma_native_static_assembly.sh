#!/usr/bin/env bash
# Source controls static module/value/type publication; extraction owns names.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ];then tail -n 35 "$work"/*.log 2>/dev/null||true;fi;rm -rf "$work";exit "$rc"' EXIT
cd "$work"
cat >target.ml <<'ML'
module type API=sig
 type t
 val value:t
 val bytes:t->bytes
 val identity:'a->'a
 val call:?enabled:bool->string->string Lwt.t
end
let prepared=ref 0
let trace=ref []
let failure=Failure "static assembly"
let fail_prepare=ref false
let context:string Lwt.key=Lwt.new_key()
let response=ref(Lwt.return "ready")
let observe=ref(fun (_:string)->())
let weak=Weak.create 1
let clock=ref(fun()->7)
let prepare()=
 trace:="package":: !trace;incr prepared;if !fail_prepare then raise failure;
 let value=Bytes.make 1048576 'x'in Weak.set weak 0(Some value);
 (module struct
  type t=bytes
  let value=value
  let bytes value=value
  let identity value=value
  let call ?(enabled=true) text=if not enabled then raise failure;(!observe)text;!response
 end:API)
let get_clock()=trace:="clock":: !trace;clock
ML
cat >target.definition <<'SOMA'
From Soma Require Import Native Handles.
OCaml Native Packed Module Type api := "Target.API".
OCaml Native External Callback prepare : unit -> api := "Target.prepare".
OCaml Native External Callback get_clock : unit -> reference(unit -> nat) := "Target.get_clock".
SOMA
cat >main.soma <<'SOMA'
From Soma Require Import Native OCaml.
From Stdlib Require Import List.
Import target.
Definition items(A:Type) := list A.
Definition identity{A:Type}(value:items A) := value.
Definition external{A:Type}(value:A) := value.
Definition unrelated := true.
Definition evidence : True := I.
Definition prepared := Native.Export(Native.Call_callback prepare tt).
Definition state := Native.Export(Native.Call_callback get_clock tt).
Definition main := ((@identity,@external),(prepared,state)).
Fail OCaml Native Static Assembly identity As "Checked" With [Value "id" := identity].
Fail OCaml Native Static Assembly main As "Bad; Injected" With [Value "id" := identity].
Fail OCaml Native Static Assembly main As "Checked" With [Value "id" := unrelated].
Fail OCaml Native Static Assembly main As "Checked" With [Value "id" := target.prepare].
Fail OCaml Native Static Assembly main As "Checked" With [Value "main" := main].
Fail OCaml Native Static Assembly main As "Checked" With [Value "id" := items].
Fail OCaml Native Static Assembly main As "Checked" With [Type "id" := identity].
Fail OCaml Native Static Assembly main As "Checked" With [Module "Package" := state].
Fail OCaml Native Static Assembly main As "Checked" With [Value "same" := identity;Value "same" := external].
Fail OCaml Native Static Assembly main As "Checked" With [Value "id;bad" := identity].
OCaml Native Static Assembly main As "Checked" With [Type "items" := items;Value "id" := identity;Value "first" := external;Value "second" := external;Value "clock" := state;Module "Package" := prepared].
Fail OCaml Native Assembly prepared As "duplicate".
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
import hashlib,shlex
rows=Path('native/native_assemblies.manifest').read_text().splitlines();assert rows[0]=='soma-native-assemblies-v1'
r=shlex.split(rows[1]);symbol,source,src_hash,name,digest,program,interface,bindings,layout,contract=r
assert symbol=='main.main'
for path,expected in [(source,src_hash),('native/'+name,digest),('native/prog.ml',program),('native/prog.mli',interface),('native/soma_bindings.ml',bindings)]:
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==expected,path
assert next(l.split()[0]for l in Path('hash.log').read_text().splitlines()if l.split()[2]==symbol)==contract
for line in Path('hash.log').read_text().splitlines():
 assumptions=set(line.split('  assumes ',1)[1].split(', '))if'  assumes 'in line else set()
 assert assumptions<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},assumptions
abi=[shlex.split(l)for l in Path('native/native_abi.manifest').read_text().splitlines()[1:]]
identity=next(i for s,_,h,i in abi if s==symbol and h==src_hash).replace('\\n','\n')
assert identity.startswith('native-static-assembly-v1\n')
assert hashlib.sha256(identity.encode()).hexdigest()==layout
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,target.ml} .
cat >check.ml <<'ML'
let require name value=if not value then failwith name
module Original=struct module Build()=struct
 module Checked:sig
  type 'a items='a list
  val identity:'a items->'a items
  val external_:'a->'a
  val prepared:(module Target.API)
  val state:(unit->int)ref
 end=struct
  type 'a items='a list
  let identity value=value
  let external_ value=value
  let prepared=Target.prepare()
  let state=Target.get_clock()
 end
 type 'a items='a Checked.items
 let id=Checked.identity
 let first=Checked.external_
 let second=Checked.external_
 let clock=Checked.state
 module Package=(val Checked.prepared)
end end
module Current=struct module Build()=struct
ML
cat native/main.assembly >>check.ml
cat >>check.ml <<'ML'
end end
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let before= !Target.prepared in
 Target.trace:=[];let module Old=Original.Build()in let old_trace=List.rev !Target.trace in
 Target.trace:=[];let module New=Current.Build()in
 require "initialization once, in source order"(!Target.prepared=before+2&&old_trace=["package";"clock"]&&old_trace=List.rev !Target.trace);
 let text=String.make 1048576 't'and data=Bytes.make 1048576 'b'in
 let values=[text]in let f x=x in
 let (_:string New.items)=values in
 require "generic aliases borrow all inputs"(New.id values==values&&New.first text==text&&New.first data==data&&New.first f==f&&New.first true);
 require "published aliases retain the same closure"(New.first==New.second&&Old.first==Old.second);
 require "original live cell"(New.clock==Target.clock&&Old.clock==Target.clock);
 Target.clock:=(fun()->91);require "later cell mutation"(!(New.clock)()=91);
 require "packed members preserve physical values"(New.Package.identity data==data&&New.Package.bytes New.Package.value==New.Package.bytes New.Package.value);
 let pending,wake=Lwt.task()and fault=Failure "package call"in let canceled=ref 0 in Lwt.on_cancel pending(fun()->incr canceled);
 List.iter(fun response->Target.response:=response;
  Target.observe:=(fun value->require "input and caller context"(value==text&&Lwt.get Target.context=Some"caller"));
  require "exact package promise"(Lwt.with_value Target.context(Some"caller")(fun()->New.Package.call text)==response))
  [Lwt.return text;pending;Lwt.fail fault];
 Target.observe:=(fun _->());Target.response:=pending;Lwt.cancel(New.Package.call text);require "exact cancellation"(!canceled=1);ignore(Sys.opaque_identity wake);
 require "optional labelled fault"(try ignore(New.Package.call ~enabled:false text);false with error->error==Target.failure);
 Target.observe:=(fun _->raise fault);require "exact synchronous fault"(try ignore(New.Package.call text);false with error->error==fault);
 Target.observe:=(fun _->());Target.response:=Lwt.return text;
 let measure call=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(call text))done;Gc.allocated_bytes()-.before in
 require "exact public call allocation"(measure Old.first=measure New.first&&measure Old.Package.call=measure New.Package.call);
 let lifetime original=
  let[@inline never] prepare()=if original then(let module V=Original.Build()in fun()->V.Package.bytes V.Package.value)
   else(let module V=Current.Build()in fun()->V.Package.bytes V.Package.value)in
  let[@inline never] retain()=let f=prepare()in collect();require "package closure retains owner"(Weak.check Target.weak 0);ignore(Sys.opaque_identity(f()))in
  retain();collect();Weak.check Target.weak 0 in
 require "original owner naturally releases"(not(lifetime true));
 require "published owner naturally releases"(not(lifetime false));
 Target.fail_prepare:=true;
 require "exact preparation fault"(try let module V=Current.Build()in ignore(Sys.opaque_identity V.first);false with error->error==Target.failure);
 print_endline "PASS: static Source modules retain generics, extraction names, type/value equations, single initialization, exact objects/promises/context/labels/faults/cancellation, call allocation and natural Weak owners."
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml check.ml
 "./check-$compiler"
done
cp hash.log before-hashes
sed -i.bak 's/Value "first" := external/Value "renamed" := external/' main.soma
soma hash main.soma -no-soma-prelude >after-hashes
python3 - <<'PY'
from pathlib import Path
def read(p):return {l.split()[2]:l.split()[0]for l in Path(p).read_text().splitlines()}
a,b=read('before-hashes'),read('after-hashes')
assert a['main.main']!=b['main.main']
assert a['main.identity']==b['main.identity']
PY
# Producer cleanup preserves edited fragments and removes unchanged obsolete ones.
cp main.soma with-assembly.soma
grep -v 'OCaml Native' with-assembly.soma >main.soma
soma extract main.soma -no-soma-prelude -o native >cleanup.log 2>&1
test ! -e native/main.assembly
test ! -e native/native_assemblies.manifest
