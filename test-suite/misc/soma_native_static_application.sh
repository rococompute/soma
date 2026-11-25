#!/usr/bin/env bash
# Typed prefix values are expanded inside the original full-application scope.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then head -n 20 "$work"/build.log 2>/dev/null || true; tail -n 35 "$work"/extract.log 2>/dev/null || true; fi; if [ "${KEEP:-0}" = 1 ]; then echo "Retained $work"; else rm -rf "$work"; fi; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
type config={mutable text:string}
let config={text="initial"}
let tag=17
let none=None
let events=ref []
let hook=ref(fun (_:string)(_ :string)->())
let note name value=events:=(name,value):: !events;!hook name value
let seen=ref []
let tokens config number variable budget ~missing text=
 note "tokens" config.text;
 seen:=[Obj.repr number;Obj.repr variable;Obj.repr budget];
 [number missing;variable text;variable budget]
let optional config ?(style=17) text=note config.text(string_of_int style);text
let generic identity tag value=ignore tag;identity value
let identity value=value
let literal prefix value=note "literal" prefix;value
let apply closure extra text=note "apply" extra;closure text
let field getter config text=config.text<-text;getter config
let read value=value
let prefix value=note "prefix" value;value
let produced literal=note "produced"literal;fun tag value->ignore tag;value
let pending=ref(Lwt.return "")
let suspended config prefix text=note config.text prefix;ignore text;!pending
let dynamic()=config
let input_slot:string Weak.t=Weak.create 1
let finish length=Gc.full_major();Gc.full_major();length,Weak.check input_slot 0
let consume config prefix ~count value=ignore config;ignore prefix;finish(String.length value+count)
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Type config := "Target.config".
OCaml Native Open Polymorphic Variant token(Row:Type) := ["N":PrimInt63.int;"V":string].
OCaml Native Construct Function number : forall Row:Type, PrimInt63.int -> token Row := "N".
OCaml Native Construct Function variable : forall Row:Type, string -> token Row := "V".
OCaml Native Callable token_target := forall Row:Type, config -> (PrimInt63.int -> token Row) -> (string -> token Row) -> string -> forall(missing:PrimInt63.int),string -> list(token Row).
OCaml Native External Value tokens : forall Row:Type, token_target Row := "Target.tokens".
OCaml Native External Value config_value : config := "Target.config".
OCaml Native External Value budget : string := "Fun.id" With "token budget".
OCaml Native Callable token_public := forall Row:Type, forall(offset:PrimInt63.int),string -> list(token Row).
OCaml Native Static Apply tokenize : forall Row:Type, token_public Row := tokens With [config_value;number;variable;budget] AtFullApplication.
OCaml Native Callable optional_target Optional style := config -> forall(style:option PrimInt63.int),string -> string.
OCaml Native External Value optional : optional_target := "Target.optional".
OCaml Native Callable optional_public Optional mode := forall(mode:option PrimInt63.int),string -> string.
OCaml Native Static Apply adjusted : optional_public := optional With [config_value] AtFullApplication.
OCaml Native External Value none_value : option PrimInt63.int := "Target.none".
OCaml Native Static Apply defaulted : string -> string := optional With [config_value;none_value] AtFullApplication.
OCaml Native External Value identity : forall A:Type,A->A := "Target.identity".
OCaml Native External Value tag : PrimInt63.int := "Target.tag".
OCaml Native External Value generic : forall A:Type,(A->A)->PrimInt63.int->A->A := "Target.generic".
OCaml Native Static Apply passthrough : forall A:Type,A->A := generic With [identity;tag] AtFullApplication.
OCaml Native External Value literal : string -> string := "Target.literal" With "/" AtFullApplication.
OCaml Native External Value apply : (string->string) -> string -> string -> string := "Target.apply".
OCaml Native Static Apply with_literal : string->string->string := apply With [literal] AtFullApplication.
OCaml Native External Value field : (config->string) -> config -> string -> string := "Target.field".
OCaml Native External Value reader : config -> string := "Target.read" Reading "text" AtFullApplication.
OCaml Native Static Apply live_field : config->string->string := field With [reader] AtFullApplication.
OCaml Native Static Apply nested : string->string := apply With [defaulted;budget] AtFullApplication.
OCaml Native External Value prefix : string := "Target.prefix" With "prefix literal".
OCaml Native External Value suspended : config->string->string->promise string := "Target.suspended".
OCaml Native Static Apply pending : string->promise string := suspended With [config_value;prefix] AtFullApplication.
OCaml Native External Value produced : PrimInt63.int -> string -> string := "Target.produced" With "producer literal".
OCaml Native Static Apply produced_call : string->string := produced With [tag] AtFullApplication.
OCaml Native Callable consume_target := config->string->forall(count:PrimInt63.int),string->(PrimInt63.int*bool).
OCaml Native External Value consume : consume_target := "Target.consume".
OCaml Native Callable consume_public := forall(count:PrimInt63.int),string->(PrimInt63.int*bool).
OCaml Native Static Apply consume_full : consume_public := consume With [config_value;budget] AtFullApplication.
OCaml Native External Callback dynamic : unit -> config := "Target.dynamic".
Fail OCaml Native Static Apply wrong_type : string->string := optional With [budget;none_value] AtFullApplication.
Fail OCaml Native Static Apply no_tail : string := optional With [config_value;none_value;budget] AtFullApplication.
Fail OCaml Native Static Apply wrong_output : string->bool := optional With [config_value;none_value] AtFullApplication.
Fail OCaml Native Static Apply wrong_arity : PrimInt63.int->string->string := optional With [config_value;none_value] AtFullApplication.
Fail OCaml Native Static Apply callback_input : string->string := optional With [dynamic;none_value] AtFullApplication.
Fail OCaml Native Construct Function wrong_payload : forall Row:Type,string->token Row := "N".
Fail OCaml Native Construct Function missing_tag : forall Row:Type,string->token Row := "Missing".
Fail OCaml Native Construct Function labelled_payload : forall Row:Type,forall(value:string),token Row := "V".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target.
Definition tokens_fn {Row:Type} := Native.Export(Native.Call_callback(tokenize Row)tt).
Definition adjusted_fn := Native.Export(Native.Call_callback adjusted tt).
Definition defaulted_fn := Native.Export(Native.Call_callback defaulted tt).
Definition passthrough_fn {A:Type} := Native.Export(Native.Call_callback(passthrough A)tt).
Definition literal_fn := Native.Export(Native.Call_callback with_literal tt).
Definition field_fn := Native.Export(Native.Call_callback live_field tt).
Definition nested_fn := Native.Export(Native.Call_callback nested tt).
Definition pending_fn := Native.Export(Native.Call_callback pending tt).
Definition produced_fn := Native.Export(Native.Call_callback produced_call tt).
Definition consume_fn := Native.Export(Native.Call_callback consume_full tt).
Definition main(Row A:Type) := (tokens_fn(Row:=Row),adjusted_fn,defaulted_fn,passthrough_fn(A:=A),literal_fn,field_fn,nested_fn,pending_fn,produced_fn,consume_fn).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes 'in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen<={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
abi=Path('native/native_abi.manifest').read_text()
assert 'static-application'in abi and 'variant-function'in abi
PY
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_callable_*.ml native/soma_variant_*.ml .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let original()=fun ~offset text->Target.tokens Target.config (fun n->`N n)(fun value->`V value)"token budget" ~missing:offset text
let current()=Soma_bindings.soma_native_746172676574_746f6b656e697a65()
let collect()=Gc.full_major();Gc.full_major()
let ids fn=ignore(fn ~offset:31 "text");!Target.seen
let matrix values=List.map(fun a->List.map((==)a)values)values
let ()=
 Target.events:=[];
 let partial=Prog.tokens_fn ~offset:31 in require "partials are quiet"(!Target.events=[]);
 Target.config.text<-"live";
 require "widened open row"(match `Extra::partial "value"with[`Extra;`N 31;`V "value";`V "token budget"]->true|_->false);
 require "live borrowed configuration"(!Target.events=["tokens","live"]);
 let old=original()and fresh=current()in
 require "closed public function native/bytecode identity"((original()==original())=(current()==current()));
 let old_ids=ids old@ids old and new_ids=ids fresh@ids fresh in
 require "constructor and literal alias matrix"(matrix old_ids=matrix new_ids);
 Target.events:=[];
 require "optional default and label translation"(Prog.adjusted_fn "default"="default"&& !Target.events=["live","17"]);
 Target.events:=[];
 require "optional override"(Prog.adjusted_fn ~mode:37 "explicit"="explicit"&& !Target.events=["live","37"]);
 Target.events:=[];require "bound omitted optional"(Prog.defaulted_fn "default"="default"&& !Target.events=["live","17"]);
 let bytes=Bytes.create 1048576 in
 require "generic bytes identity"(Prog.passthrough_fn bytes==bytes);
 let callback()=bytes in require "generic function identity"(Prog.passthrough_fn callback==callback);
 Target.events:=[];let next=Prog.literal_fn "extra"in require "literal callback creation is quiet"(!Target.events=[]);
 require "literal callback invoked only by target"(next "value"="value"&&List.map fst(List.rev !Target.events)=["apply";"literal"]);
 let cfg={Target.text="stale"}in require "field read waits for callback invocation"(Prog.field_fn cfg "changed"="changed");
 Target.events:=[];require "nested static arguments"(Prog.nested_fn "nested"="nested"&&List.map fst(List.rev !Target.events)=["apply";"live"]);
 Target.events:=[];require "function-valued getter runs at full call"(Prog.produced_fn "value"="value"&& !Target.events=["produced","producer literal"]);
 let fault=Failure "exact native fault"in
 Target.hook:=(fun _ _->raise fault);
 require "exact synchronous exception"(try ignore(Prog.tokens_fn ~offset:0 "text");false with error->error==fault);
 Target.hook:=(fun _ _->());
 let promise,_=Lwt.task()in Target.pending:=promise;
 let key=Lwt.new_key()in Target.hook:=(fun _ _->require "caller Lwt context"(Lwt.get key=Some "caller"));
 Lwt.with_value key(Some "caller")(fun()->require "exact borrowed promise"(Prog.pending_fn "input"==promise));
 Lwt.cancel promise;require "cancellation"(match Lwt.state promise with Lwt.Fail Lwt.Canceled->true|_->false);
 Target.hook:=(fun _ _->());Target.events:=[];Target.seen:=[];
 let measure fn=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(fn()))done;Gc.allocated_bytes()-.before in
 let same name old current=let a=measure old and b=measure current in
  Printf.printf "%s %.0f/%.0f B\n%!"name a b;require name(a=b)in
 same "full wrapper creation"original current;
 let run fn=let result=fn ~offset:31 "text"in Target.events:=[];Target.seen:=[];result in
 same "full wrapper invocation"(fun()->run old)(fun()->run fresh);
 let released fn=let weak=Weak.create 1 in
  let[@inline never] invoke()=let text=Bytes.to_string(Bytes.make 1048576 'w')in Weak.set weak 0(Some text);
   ignore(Sys.opaque_identity(fn ~offset:31 text));Target.events:=[];Target.seen:=[]in
  invoke();collect();not(Weak.check weak 0)in
 require "full calls release borrowed input"(released old&&released fresh);
 let retained fn=let weak=Weak.create 1 in
  let[@inline never] prepare()=let text=Bytes.to_string(Bytes.make 1048576 'p')in Weak.set weak 0(Some text);fun()->fn ~offset:31 text in
  let[@inline never] hold()=let partial=prepare()in collect();require "partial input remains live"(Weak.check weak 0);
   ignore(Sys.opaque_identity(partial()));Target.events:=[];Target.seen:=[]in
  hold();collect();not(Weak.check weak 0)in
 require "partial calls release input after drop"(retained old&&retained fresh);
 let original_consume ~count text=Target.consume Target.config "token budget" ~count text in
 let[@inline never] consuming fn=let text=Bytes.to_string(Bytes.make 1048576 'c')in
  Weak.set Target.input_slot 0(Some text);fn ~count:7 text in
 let a=consuming original_consume and b=consuming Prog.consume_fn in
 require "original consuming frame sensitivity"(a=(1048583,false));
 require "exact consumed-owner frame during target tail continuation"(a=b);
 print_endline "PASS: typed static prefix arguments preserve constructor/literal creation phases, full-call scope, labels/defaults/generics, aliases, faults, promises/context/cancellation, exact allocation and Weak lifetimes."
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_variant_*.ml soma_callable_*.ml soma_bindings.ml prog.mli prog.ml check.ml
 ./"check-$compiler"
done
cp native/native_abi.manifest before-abi
cp hash.log before-hash
sed -i.bak 's/token budget/changed budget/' target.definition
soma extract main.soma -no-soma-prelude -o changed >changed.log 2>&1
soma hash main.soma -no-soma-prelude >changed-hash
if cmp -s before-abi changed/native_abi.manifest;then echo 'static bound literal ABI did not change' >&2;exit 1;fi
if cmp -s before-hash changed-hash;then echo 'static bound literal semantic hashes did not change' >&2;exit 1;fi
