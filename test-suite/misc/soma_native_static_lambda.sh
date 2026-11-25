#!/usr/bin/env bash
# Typed nested callables keep their native lexical scope and ownership.
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
let saved:(string->string Lwt.t)option ref=ref None
let pending=ref(Lwt.return "")
let store owner callback text=note "store";ignore(owner,text);saved:=Some callback;Lwt.return_unit
let execute owner prefix text=note "execute";ignore(owner,prefix,text);!pending
let dispatch callback text=note "dispatch";callback text
let with_inner callback ~suffix text=note "inner";callback ~suffix text
let finish owner prefix first suffix last=note "finish";owner.text^prefix^first^suffix^last
let invoke_optional (callback : ?suffix:string->string->string) text=callback text
let optional_finish owner suffix text=owner.text^Option.value ~default:"default"suffix^text
let trigger()=note "trigger"
let drop_callback _callback text=text
let identity value=value
let apply callback value=callback value
let slot:owner Weak.t=Weak.create 1
let consume size=Gc.full_major();Gc.full_major();size,Weak.check slot 0
let size owner text=String.length(owner.text^text)
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Type owner := "Target.owner".
OCaml Native Callable callback := string->promise string.
OCaml Native External Value store : owner->callback->string->promise unit := "Target.store".
OCaml Native External Value execute : owner->string->string->promise string := "Target.execute".
OCaml Native Static Invoke prepare : owner->string->promise unit := store With
 [Argument 0;Function callback [Call execute [Argument 0;Argument 1;Argument 2]];Argument 1] AtFullApplication.
OCaml Native Callable outer := string->string.
OCaml Native Callable inner := forall(suffix:string),string->string.
OCaml Native External Value dispatch : outer->string->string := "Target.dispatch".
OCaml Native Callable inner_target := inner->forall(suffix:string),string->string.
OCaml Native External Value with_inner : inner_target := "Target.with_inner".
OCaml Native External Value finish : owner->string->string->string->string->string := "Target.finish".
OCaml Native Static Invoke nested : owner->string->string->string := dispatch With
 [Function outer [Call with_inner [Function inner [Call finish [Argument 0;Argument 1;Argument 3;Argument 4;Argument 5]];Argument 1;Argument 3]];Argument 2] AtFullApplication.
OCaml Native Callable optional_callback Optional suffix := forall(suffix:option string),string->string.
OCaml Native External Value invoke_optional : optional_callback->string->string := "Target.invoke_optional".
OCaml Native External Value optional_finish : owner->option string->string->string := "Target.optional_finish".
OCaml Native Static Invoke optional_fn : owner->string->string := invoke_optional With
 [Function optional_callback [Call optional_finish [Argument 0;Argument 2;Argument 3]];Argument 1] AtFullApplication.
OCaml Native Callable unused_signature := string->string.
OCaml Native External Value drop_callback : unused_signature->string->string := "Target.drop_callback".
OCaml Native External Value ignored_result : string := "Fun.id" With "ignored".
OCaml Native Static Invoke ignored_fn : string->string := drop_callback With
 [Function unused_signature [Value ignored_result];Argument 0] AtFullApplication.
OCaml Native Callable generic := forall A:Type,A->A.
OCaml Native External Value apply : forall A:Type,generic A->A->A := "Target.apply".
OCaml Native External Value identity : forall A:Type,A->A := "Target.identity".
OCaml Native Static Invoke generic_fn : forall A:Type,A->A := apply With
 [Function generic [Call identity [Argument 1]];Argument 0] AtFullApplication.
OCaml Native Callable consume_callback := string->(PrimInt63.int*bool).
OCaml Native External Value consume : PrimInt63.int->(PrimInt63.int*bool) := "Target.consume".
OCaml Native External Value size : owner->string->PrimInt63.int := "Target.size".
OCaml Native External Value consume_apply : consume_callback->string->(PrimInt63.int*bool) := "Target.apply".
OCaml Native Static Invoke consume_fn : owner->string->(PrimInt63.int*bool) := consume_apply With
 [Function consume_callback [Call consume [Call size [Argument 0;Argument 2]]];Argument 1] AtFullApplication.
OCaml Native Assertion Function invalid : forall A:Type,A->string := 37 9.
OCaml Native Assertion Function invalid_unit : unit->string := 37 9.
OCaml Native External Value trigger : unit->unit := "Target.trigger".
OCaml Native Static Invoke direct_assert : unit->string := invalid_unit With [Call trigger [Argument 0]] AtFullApplication.
OCaml Native Callable failure := unit->string.
OCaml Native External Value run_failure : (unit->string)->unit->string := "Target.apply".
OCaml Native Static Invoke assert_fn : unit->string := run_failure With [Value invalid_unit;Argument 0] AtFullApplication.
Fail OCaml Native Static Invoke bad_index : owner->string->promise unit := store With
 [Argument 0;Function callback [Call execute [Argument 0;Argument 1;Argument 3]];Argument 1] AtFullApplication.
Fail OCaml Native Static Invoke bad_result : owner->string->promise unit := store With
 [Argument 0;Function callback [Call identity [Argument 2]];Argument 1] AtFullApplication.
Fail OCaml Native Static Invoke not_callable : owner->string->promise unit := store With
 [Argument 0;Function execute [Argument 2];Argument 1] AtFullApplication.
Fail OCaml Native Static Invoke escaped_scope : owner->string->promise unit := store With
 [Argument 0;Function callback [Call execute [Argument 0;Argument 1;Argument 2]];Argument 2] AtFullApplication.
Fail OCaml Native Assertion Function bad_arity : unit->unit->string := 37 9.
Fail OCaml Native Assertion Function bad_label : forall(value:unit),string := 37 9.
Fail OCaml Native Assertion Function bad_location : unit->string := 0 9.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target.
Definition prepare_fn := Native.Export(Native.Call_callback prepare tt).
Definition direct_asserting := Native.Export(Native.Call_callback direct_assert tt).
Definition ignored_run := Native.Export(Native.Call_callback ignored_fn tt).
Definition optional_run := Native.Export(Native.Call_callback optional_fn tt).
Definition nested_fn := Native.Export(Native.Call_callback nested tt).
Definition generic_run{A:Type} := Native.Export(Native.Call_callback(generic_fn A)tt).
Definition consuming_fn := Native.Export(Native.Call_callback consume_fn tt).
Definition invalid_fn{A:Type} := Native.Export(Native.Call_callback(invalid A)tt).
Definition asserting_fn := Native.Export(Native.Call_callback assert_fn tt).
Definition main(A:Type) := (prepare_fn,nested_fn,generic_run(A:=A),consuming_fn,invalid_fn(A:=A),asserting_fn,optional_run,ignored_run,direct_asserting).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
abi=Path('native/native_abi.manifest').read_text();assert 'lambda ['in abi and 'assertion-function line 37 column 9'in abi
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_callable_*.ml .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let collect()=Gc.full_major();Gc.full_major()
let original()=fun owner text->Target.store owner (fun value->Target.execute owner text value)text
let current()=Soma_bindings.soma_native_746172676574_70726570617265()
let original_nested()=fun owner prefix text->Target.dispatch(fun first->Target.with_inner(fun ~suffix last->Target.finish owner prefix first suffix last)~suffix:prefix first)text
let current_nested()=Soma_bindings.soma_native_746172676574_6e6573746564()
let owner()={Target.text="live"}
let clear()=Target.saved:=None;Target.events:=[]
let ()=
 require "closed root native/BC sharing"((original()==original())=(current()==current()));
 require "nested root native/BC sharing"((original_nested()==original_nested())=(current_nested()==current_nested()));
 let old=original()and fresh=current()in
 clear();let io=owner()in let partial=fresh io in require "quiet outer partial"(!Target.events=[]&& !Target.saved=None);
 ignore(partial "prefix");require "captured callback not invoked early"(!Target.events=["store"]);
 let callback=Option.get !Target.saved in
 let pending,_=Lwt.task()in Target.pending:=pending;
 let context=Lwt.new_key()in Target.hook:=(fun _->require "caller context"(Lwt.get context=Some 31));
 Lwt.with_value context(Some 31)(fun()->require "exact pending promise"(callback "value"==pending));
 Lwt.cancel pending;require "exact cancellation"(match Lwt.state pending with Lwt.Fail Lwt.Canceled->true|_->false);
 Target.hook:=(fun _->());clear();
 let io=owner()in let run=Prog.nested_fn io "P"in io.text<-"changed";
 require "nested lexical arguments/label"(run "T"="changedPTPT");
 require "nested invocation order"(List.rev !Target.events=["dispatch";"inner";"finish"]);
 List.iter(fun stage->let fault=Failure stage in
  let run fn=clear();Target.hook:=(fun at->if at=stage then raise fault);
   require "exact nested fault"(try ignore(fn(owner())"P""T");false with error->error==fault);
   Target.hook:=(fun _->());List.rev !Target.events in
  require "exact nested failure prefix"(run(original_nested())=run(current_nested()))
 )["dispatch";"inner";"finish"];
 require "unused typed lambda input"(Prog.ignored_run "borrowed"="borrowed");
 require "optional nested callback omission"(Prog.optional_run(owner())"x"="livedefaultx");
 let bytes=Bytes.make 4096 'b'in require "generic nested bytes"(Prog.generic_run bytes==bytes);
 let closure()=bytes in require "generic nested closure"(Prog.generic_run closure==closure);
 let check_invalid fn=try ignore(fn());failwith "missing assertion"with Assert_failure(file,line,column)->require "assertion declaration location"(Filename.basename file="soma_bindings.ml"&&line=37&&column=9)in
 check_invalid Prog.invalid_fn;check_invalid Prog.asserting_fn;
 clear();check_invalid Prog.direct_asserting;require "ignored assertion argument evaluated"(!Target.events=["trigger"]);
 let weak=Weak.create 1 in
 let[@inline never] prepare fn=let io=owner()in Weak.set weak 0(Some io);ignore(fn io "prefix")in
 prepare old;collect();require "old stored callback retains owner"(Weak.check weak 0);clear();collect();require "old dropped callback releases owner"(not(Weak.check weak 0));
 prepare fresh;collect();require "new stored callback retains owner"(Weak.check weak 0);clear();collect();require "new dropped callback releases owner"(not(Weak.check weak 0));
 let old_consume io text=Target.apply(fun value->Target.consume(Target.size io value))text in
 let[@inline never] consume fn=let io={Target.text=Bytes.to_string(Bytes.make 1048576 'o')}in Weak.set Target.slot 0(Some io);fn io "x"in
 let a=consume old_consume and b=consume Prog.consuming_fn in require "consumed owner collection sensitivity"(a=(1048577,false));require "nested callback tail continuation lifetime"(a=b);
 let measure fn=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.before in
 let same name a b=let x=measure a and y=measure b in Printf.printf "%s %.0f/%.0f B\n%!"name x y;require name(x=y)in
 same "root creation"original current;
 let io=owner()in
 let invoke fn=let value=fn io "text"in clear();value in
 same "captured callback invocation allocation"(fun()->invoke old)(fun()->invoke fresh);
 let invoke fn=let value=fn io "P""T"in clear();value in
 same "nested callback allocation"(fun()->invoke(original_nested()))(fun()->invoke(current_nested()));
 print_endline "PASS: checked nested callable scopes preserve Native/BC sharing, generics, labels, live captures, exact exceptions/promises/context/cancellation, exact allocation and natural Weak/tail-continuation lifetimes."
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml $(ocamldep -sort soma_callable_*.ml) soma_bindings.ml prog.mli prog.ml check.ml
 ./"check-$compiler"
done
cp target.definition before-definition
cp native/native_abi.manifest before-abi
cp hash.log before-hash
sed -i.bak 's/Argument 0;Argument 1;Argument 3;Argument 4;Argument 5/Argument 0;Argument 3;Argument 1;Argument 4;Argument 5/' target.definition
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash
if cmp -s before-abi changed/native_abi.manifest;then echo 'lambda capture ABI unchanged' >&2;exit 1;fi
if cmp -s before-hash changed-hash;then echo 'lambda capture semantic hash unchanged' >&2;exit 1;fi
cp before-definition target.definition
sed -i.bak 's/Callable unused_signature := string->string/Callable unused_signature := unit->string/' target.definition
soma extract main.soma -no-soma-prelude -o type-changed >type-changed.log 2>&1
soma hash main.soma -no-soma-prelude >type-changed-hash
if cmp -s before-abi type-changed/native_abi.manifest;then echo 'unused lambda domain ABI unchanged' >&2;exit 1;fi
if cmp -s before-hash type-changed-hash;then echo 'unused lambda domain semantic hash unchanged' >&2;exit 1;fi
