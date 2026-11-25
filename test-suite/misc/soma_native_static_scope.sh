#!/usr/bin/env bash
# A jointly prepared inner/composed pair retains the original closure graph.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 45 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
type owner={mutable payload:string}
let hook=ref(fun (_:string)(_ :string)->())
let get owner literal= !hook "get" literal;owner.payload
let outer value missing path= !hook "outer" path;ignore missing;value
let identity x=x
let keep value extra=ignore extra;value
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "Target.owner".
OCaml Native External Value get : owner -> string := "Target.get" With "/" After 1 AtFullApplication.
OCaml Native External Value outer : string -> PrimInt63.int -> string -> string := "Target.outer".
OCaml Native Callable public_call := owner -> forall(missing:PrimInt63.int), string -> string.
OCaml Native Static Compose Scope prepared : ((owner -> string) * public_call) := outer With get.
OCaml Native External Value identity : forall A:Type, A -> A := "Target.identity".
OCaml Native External Value keep : forall A:Type, A -> string -> A := "Target.keep".
OCaml Native Static Compose Scope generic : forall A:Type, ((A -> A) * (A -> string -> A)) := keep With identity.
Fail OCaml Native Static Compose Scope missing_pair : public_call := outer With get.
Fail OCaml Native Static Compose Scope wrong_inner : ((string -> string) * public_call) := outer With get.
Fail OCaml Native Static Compose Scope wrong_result : ((owner -> string) * (owner -> PrimInt63.int -> string -> bool)) := outer With get.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
From Stdlib Require Import Strings.String.
Import target.
Definition prepared_pair := Native.Export(Native.Call_callback prepared tt).
Definition generic_pair := Native.Export(Native.Call_callback(generic string)tt).
Definition main := (prepared_pair,generic_pair).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_callable_*.ml .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let original()=
 let inner owner=Target.get owner "/"in
 let composed owner ~missing path=Target.outer(inner owner)missing path in
 inner,composed
let fresh()=Soma_bindings.soma_native_746172676574_7072657061726564()
let matrix xs=List.map(fun a->List.map((==)a)xs)xs
let ids (a,b)=[Obj.repr a;Obj.repr b]
let collect()=Gc.full_major();Gc.full_major()
let ()=
 let old_inner,old=original()and new_inner,current=fresh()in
 let owner={Target.payload=String.make 1048576 'a'}in
 let events=ref []in Target.hook:=(fun event value->events:=(event,value):: !events);
 let old_partial=old owner and partial=current owner in require "partials quiet"(!events=[]);
 owner.payload<-String.make 1048576 'b';
 require "live borrowed result"(old_partial ~missing:0 "path"==owner.payload&&partial ~missing:0 "path"==owner.payload);
 let literal inner outer=let seen=ref []in Target.hook:=(fun event value->if event="get"then seen:=value:: !seen);
  ignore(inner owner);ignore(outer owner ~missing:0 "path");match !seen with[a;b]->a==b|_->false in
 require "one original literal origin"(literal old_inner old);
 require "one shared compiled literal origin"(literal new_inner current);
 require "native/bytecode inner/composed identity matrix"(matrix(ids(original())@ids(original()))=matrix(ids(fresh())@ids(fresh())));
 let fault=Failure "scope call"in Target.hook:=(fun _ _->raise fault);
 require "direct synchronous fault"(try ignore(current owner ~missing:0 "path");false with error->error==fault);
 Target.hook:=(fun _ _->());
 let first,second=Prog.generic_pair in let x=String.make 1048576 'g'in
 require "borrowed existing function"(first==Target.identity);
 require "generic borrowed payload"(second x "extra"==x);
 let measure fn=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.before in
 let a=measure original and b=measure fresh in
 require "exact scope construction allocation"(a=b);
 let c=measure(fun()->old owner ~missing:0 "path")and d=measure(fun()->current owner ~missing:0 "path")in
 require "exact scope invocation allocation"(c=d);
 let graph factory=
  let weak=Weak.create 1 in
  let[@inline never] prepare()=let inner,outer=factory()in Weak.set weak 0(Some inner);outer in
  let outer=prepare()in collect();let alive=Weak.check weak 0 in
  ignore(Sys.opaque_identity(outer owner ~missing:0 "path"));alive in
 require "composed function retains its exported inner function"(graph original=graph fresh);
 let release factory=
  let weak=Weak.create 2 in
  let[@inline never] prepare()=let inner,outer=factory()in Weak.set weak 0(Some(Obj.repr inner));Weak.set weak 1(Some(Obj.repr outer));()in
  prepare();collect();Weak.check weak 0,Weak.check weak 1 in
 require "scope closures release like original"(release original=release fresh);
 let owner_release fn=let weak=Weak.create 1 in
  let[@inline never] invoke()=let owner={Target.payload=String.make 1048576 'w'}in Weak.set weak 0(Some owner);ignore(Sys.opaque_identity(fn owner ~missing:0 "path"))in
  invoke();collect();not(Weak.check weak 0)in
 require "no retained caller ownership"(owner_release old&&owner_release current);
 Printf.printf "PASS: static composition scope preserves aliases, literal origin, full-call phases, exact faults, caller/inner closure Weak graph, generic values and exact creation %.0f/%.0f and invocation %.0f/%.0f B.\n%!"a b c d
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_callable_*.ml soma_bindings.ml prog.mli prog.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
cp hash.log before-hash
sed -i.bak 's/With "\/" After 1/With "changed" After 1/' target.definition
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash
if cmp -s before-abi changed/native_abi.manifest;then echo 'scope ABI failed to change' >&2;exit 1;fi
if cmp -s before-hash changed-hash;then echo 'scope semantic hashes failed to change' >&2;exit 1;fi
