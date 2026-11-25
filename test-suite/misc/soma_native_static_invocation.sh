#!/usr/bin/env bash
# Fully checked argument trees expand as closed native full-application bodies.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 40 "$work"/{extract,build}.log 2>/dev/null || true; fi; if [ "${KEEP:-0}" = 1 ]; then echo "Retained $work"; else rm -rf "$work"; fi; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
type owner={mutable text:string}
let events=ref []
let hook=ref(fun (_:string)->())
let note stage=events:=stage:: !events;!hook stage
let seen=ref []
let reader owner=note "reader";fun key->owner.text^key
let setter owner=note "setter";fun key value->owner.text<-key^value
let arithmetic owner=note "arithmetic";fun text->String.length(owner.text^text)
let evaluate owner native effects get set arithmetic dbl text=
 note "evaluate";seen:=[Obj.repr owner;Obj.repr native;Obj.repr effects;Obj.repr get;Obj.repr set;Obj.repr arithmetic];
 let value=effects(get text)in
 let value=native value in
 if dbl then set text value;
 arithmetic value
let identity x=x
let generic identity value=identity value
let optional prefix ?(mode=7) text=note "optional";prefix^string_of_int mode^text
let prefix text=note "prefix";"["^text^"]"
let pending=ref(Lwt.return "")
let suspended prefix text=note "suspended";ignore(prefix,text);!pending
let tokens number literal text=note "tokens";seen:=[Obj.repr number;Obj.repr literal];[number(String.length text)]
let integer x=x
let dynamic()="forbidden"
let owner_slot:owner Weak.t=Weak.create 1
let finish length=Gc.full_major();Gc.full_major();length,Weak.check owner_slot 0
let consume length=finish length
let length owner=String.length owner.text
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String Lists.List.
OCaml Native External Type owner := "Target.owner".
Local Abbreviation map := (string->string).
OCaml Native External Value evaluate : owner->map->map->map->(string->string->unit)->(string->PrimInt63.int)->bool->string->PrimInt63.int := "Target.evaluate".
OCaml Native External Value reader : owner->map := "Target.reader".
OCaml Native External Value setter : owner->string->string->unit := "Target.setter".
OCaml Native External Value arithmetic : owner->string->PrimInt63.int := "Target.arithmetic".
OCaml Native Callable public := forall(native_map:map)(effects_map:map),owner->forall(dbl:bool),string->PrimInt63.int.
OCaml Native Static Invoke run : public := evaluate With [Argument 2;Argument 0;Argument 1;Call reader [Argument 2];Call setter [Argument 2];Call arithmetic [Argument 2];Argument 3;Argument 4] AtFullApplication.
OCaml Native External Value identity : forall A:Type,A->A := "Target.identity".
OCaml Native External Value generic : forall A:Type,(A->A)->A->A := "Target.generic".
OCaml Native Static Invoke generic_run : forall A:Type,A->A := generic With [Value identity;Argument 0] AtFullApplication.
OCaml Native Callable optional_target Optional mode := string->forall(mode:option PrimInt63.int),string->string.
OCaml Native External Value optional : optional_target := "Target.optional".
OCaml Native External Value prefix : string->string := "Target.prefix".
OCaml Native Callable optional_public Optional style := forall(style:option PrimInt63.int),string->string.
OCaml Native Static Invoke optional_run : optional_public := optional With [Call prefix [Argument 1];Argument 0;Argument 1] AtFullApplication.
OCaml Native External Value suspended : string->string->promise string := "Target.suspended".
OCaml Native Static Invoke pending_run : string->promise string := suspended With [Call prefix [Argument 0];Argument 0] AtFullApplication.
OCaml Native Open Polymorphic Variant token(Row:Type) := ["N":PrimInt63.int].
OCaml Native Construct Function number : forall Row:Type,PrimInt63.int->token Row := "N".
OCaml Native Static Invoke number_call : forall Row:Type,PrimInt63.int->token Row := number With [Argument 0] AtFullApplication.
OCaml Native External Value tokens : forall Row:Type,(PrimInt63.int->token Row)->string->string->list(token Row) := "Target.tokens".
OCaml Native External Value literal : string := "Fun.id" With "literal".
OCaml Native Static Invoke token_run : forall Row:Type,string->list(token Row) := tokens With [Value number;Value literal;Argument 0] AtFullApplication.
OCaml Native External Value consume : PrimInt63.int->(PrimInt63.int*bool) := "Target.consume".
OCaml Native External Value length : owner->PrimInt63.int := "Target.length".
OCaml Native Static Invoke consuming : owner->(PrimInt63.int*bool) := consume With [Call length [Argument 0]] AtFullApplication.
OCaml Native External Callback dynamic : unit->string := "Target.dynamic".
Fail OCaml Native Static Invoke bad_index : string->string := prefix With [Argument 1] AtFullApplication.
Fail OCaml Native Static Invoke bad_nested : owner->string := prefix With [Call length [Argument 0]] AtFullApplication.
Fail OCaml Native Static Invoke bad_result : string->bool := prefix With [Argument 0] AtFullApplication.
Fail OCaml Native Static Invoke bad_arity : string->string := prefix With [Argument 0;Argument 0] AtFullApplication.
Fail OCaml Native Static Invoke bad_partial : owner->PrimInt63.int := consume With [Call evaluate [Argument 0]] AtFullApplication.
Fail OCaml Native Static Invoke bad_callback : string->string := prefix With [Value dynamic] AtFullApplication.
Fail OCaml Native Static Invoke bad_value : owner->string := prefix With [Value evaluate] AtFullApplication.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target.
Definition run_fn := Native.Export(Native.Call_callback run tt).
Definition generic_fn{A:Type} := Native.Export(Native.Call_callback(generic_run A)tt).
Definition optional_fn := Native.Export(Native.Call_callback optional_run tt).
Definition pending_fn := Native.Export(Native.Call_callback pending_run tt).
Definition number_fn{Row:Type} := Native.Export(Native.Call_callback(number_call Row)tt).
Definition token_fn{Row:Type} := Native.Export(Native.Call_callback(token_run Row)tt).
Definition consuming_fn := Native.Export(Native.Call_callback consuming tt).
Definition main(A Row:Type) := (run_fn,generic_fn(A:=A),optional_fn,pending_fn,token_fn(Row:=Row),consuming_fn,number_fn(Row:=Row)).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
assert 'static-invocation'in Path('native/native_abi.manifest').read_text()
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_callable_*.ml native/soma_variant_*.ml .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let original()=fun ~native_map ~effects_map owner ~dbl text->Target.evaluate owner native_map effects_map (Target.reader owner)(Target.setter owner)(Target.arithmetic owner)dbl text
let current()=Soma_bindings.soma_native_746172676574_72756e()
let collect()=Gc.full_major();Gc.full_major()
let matrix values=List.map(fun a->List.map((==)a)values)values
let owner()={Target.text="initial"}
let identity value=value
let call fn=fn ~native_map:identity ~effects_map:identity(owner())~dbl:false "input"
let ()=
 require "closed Native/BC identity"((original()==original())=(current()==current()));
 let old=original()and fresh=current()in
 Target.events:=[];let partial=fresh ~native_map:identity ~effects_map:identity in
 require "labelled partials quiet"(!Target.events=[]);
 let io=owner()in let final=partial io ~dbl:false in io.text<-"live";
 require "owner read after final application"(final "input"=String.length("liveliveinput"));
 require "original right-to-left derivation order"(List.rev !Target.events=["arithmetic";"setter";"reader";"evaluate"]);
 List.iter(fun stage->
  let error=Failure stage in
  let run fn=Target.events:=[];Target.hook:=(fun at->if at=stage then raise error);
   require "exact exception"(try ignore(call fn);false with caught->caught==error);
   Target.hook:=(fun _->());List.rev !Target.events in
  require "exact failure prefix"(run old=run fresh)
 )["arithmetic";"setter";"reader";"evaluate"];
 let ids fn=ignore(call fn);!Target.seen in
 require "derived callback alias matrix"(matrix(ids old@ids old)=matrix(ids fresh@ids fresh));
 let bytes=Bytes.make 4096 'b'in require "generic bytes borrowed"(Prog.generic_fn bytes==bytes);
 let closure()=bytes in require "generic closure borrowed"(Prog.generic_fn closure==closure);
 Target.events:=[];require "optional default"(Prog.optional_fn "x"="[x]7x");
 require "nested optional derivation"(List.rev !Target.events=["prefix";"optional"]);
 require "optional override"(Prog.optional_fn ~style:31 "x"="[x]31x");
 let promise,_=Lwt.task()in Target.pending:=promise;let context=Lwt.new_key()in
 Target.hook:=(fun _->require "caller Lwt context"(Lwt.get context=Some 37));
 Lwt.with_value context(Some 37)(fun()->require "exact pending promise"(Prog.pending_fn "input"==promise));
 Lwt.cancel promise;require "cancellation"(match Lwt.state promise with Lwt.Fail Lwt.Canceled->true|_->false);
 Target.hook:=(fun _->());
 require "independently widened row one"(match `Extra::Prog.token_fn "abc"with[`Extra;`N 3]->true|_->false);
 require "independently widened row two"(match `Other 1::Prog.token_fn "x"with[`Other 1;`N 1]->true|_->false);
 require "direct typed constructor call"(match `Other::[Prog.number_fn 7]with[`Other;`N 7]->true|_->false);
 let tokens text=Target.tokens(fun n->`N n)"literal"text in
 let ids fn=ignore(fn "value");!Target.seen in
 require "per-full-call constructor and literal identity"(matrix(ids tokens@ids tokens)=matrix(ids Prog.token_fn@ids Prog.token_fn));
 let measure fn=collect();let start=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.start in
 let same name a b=let x=measure a and y=measure b in Printf.printf "%s %.0f/%.0f B\n%!"name x y;require name(x=y)in
 same "wrapper creation"original current;
 let invoke fn=let value=call fn in Target.events:=[];Target.seen:=[];value in
 same "full call allocation"(fun()->invoke old)(fun()->invoke fresh);
 let weak=Weak.create 1 in
 let[@inline never] prepare fn=let io=owner()in Weak.set weak 0(Some io);fn ~native_map:identity ~effects_map:identity io ~dbl:false in
 let hold fn=let partial=prepare fn in collect();require "partial retains borrowed owner"(Weak.check weak 0);ignore(Sys.opaque_identity(partial "x"));Target.seen:=[]in
 hold old;collect();require "old dropped partial releases owner"(not(Weak.check weak 0));
 hold fresh;collect();require "new dropped partial releases owner"(not(Weak.check weak 0));
 let old_consume io=Target.consume(Target.length io)in
 let[@inline never] consuming fn=let io={Target.text=Bytes.to_string(Bytes.make 1048576 'x')}in Weak.set Target.owner_slot 0(Some io);fn io in
 let a=consuming old_consume and b=consuming Prog.consuming_fn in
 require "original owner collection sensitivity"(a=(1048576,false));
 require "consumed owner frame inside target tail continuation"(a=b);
 print_endline "PASS: typed argument trees preserve closed sharing, repeated/live arguments, right-to-left faults, labels/defaults, generic/open-row APIs, callback/literal identities, exact promises/context/cancellation/allocation and natural Weak lifetimes."
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_callable_*.ml soma_variant_*.ml soma_bindings.ml prog.mli prog.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
cp hash.log before-hash
cp target.definition before-definition
sed -i.bak 's/Call reader \[Argument 2\]/Value reader/' target.definition
if soma extract main.soma -no-soma-prelude -o invalid >invalid.log 2>&1;then echo 'accepted wrong higher-order domain' >&2;exit 1;fi
cp before-definition target.definition
sed -i.bak 's/Argument 0;Argument 1;Call reader/Argument 1;Argument 0;Call reader/' target.definition
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash
if cmp -s before-abi changed/native_abi.manifest;then echo 'argument order ABI unchanged' >&2;exit 1;fi
if cmp -s before-hash changed-hash;then echo 'argument order semantic hash unchanged' >&2;exit 1;fi
