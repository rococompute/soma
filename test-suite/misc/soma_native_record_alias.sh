#!/usr/bin/env bash
# Borrow checked parametric records through exact native type equations.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat > producer.soma <<'SOMA'
From Stdlib Require Import List Strings.String.
Record entry (A B : Type) := Entry {
 name : string; values : list A; callback : A -> B
}.
Record nested (A B : Type) := Nested { nested_callback : (A -> B) -> A -> B }.
Record singleton := Singleton { text : string }.
Record dependent := Dependent { shape : Type; payload : shape }.
Record indexed (n : nat) := Indexed { indexed_value : nat }.
Record evidence : Prop := Evidence { proof : True }.
Record proof_field := Proof_field { proof_value : True }.
Record polymorphic_field := Polymorphic_field { polymorphic_value : forall A : Type, A -> A }.
CoInductive recursive := Recursive { next : recursive }.
Inductive variant := First | Second.
Definition main := tt.
SOMA
cat > target.ml <<'ML'
type ('a,'b) entry = { name:string; values:'a list; callback:'a -> 'b }
type ('a,'b) nested = { nested_callback : ('a -> 'b) -> 'a -> 'b }
type singleton = { text:string }
let invoke ?(enabled=true) text=enabled,text
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native.
Import producer.
OCaml Native Record Alias entry := producer.entry As "Target.entry".
OCaml Native Record Alias nested := producer.nested As "Target.nested".
OCaml Native Record Alias singleton := producer.singleton As "Target.singleton".
Local Definition entry_alias (A B : Type) := producer.entry A B.
OCaml Native External Value borrowed_entry : forall A B : Type, entry_alias A B -> entry_alias A B := "Fun.id".
OCaml Native Callable invocation Optional enabled := forall (enabled : option bool), string -> bool * string.
Local Definition invocation_alias := invocation.
Local Definition invocation_twice := invocation_alias.
OCaml Native External Value borrowed_invocation : invocation_twice := "Target.invoke".
OCaml Native Apply invoke_call : invocation -> option bool -> string -> bool * string.
Fail OCaml Native Variant Alias mixed := producer.singleton As "Target.singleton".
Fail OCaml Native Record Alias conflict := producer.entry As "Other.entry".
Fail OCaml Native Record Alias dependent := producer.dependent As "Target.dependent".
Fail OCaml Native Record Alias indexed := producer.indexed As "Target.indexed".
Fail OCaml Native Record Alias evidence := producer.evidence As "Target.evidence".
Fail OCaml Native Record Alias proof_field := producer.proof_field As "Target.proof_field".
Fail OCaml Native Record Alias polymorphic_field := producer.polymorphic_field As "Target.polymorphic_field".
Fail OCaml Native Record Alias recursive := producer.recursive As "Target.recursive".
Fail OCaml Native Record Alias variant := producer.variant As "Target.variant".
Fail OCaml Native Record Alias injected := producer.entry As "Target.entry; assert false".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target producer.
Definition identity {A B : Type} (value : entry A B) := value.
Definition call {A B : Type} (value : producer.entry A B) argument := callback A B value argument.
Definition pack {A B : Type} name values callback := @Entry A B name values callback.
Definition only (value : producer.singleton) := text value.
Definition single name := Singleton name.
Definition view {A B : Type} (value : producer.entry A B) :=
 match value with Entry _ _ name values callback => (name,values,callback) end.
Definition invoke enabled text := Native.Export (
 Native.Bind (Native.Call_callback borrowed_invocation tt) (fun invoke =>
  Native.Call_callback invoke_call (invoke,(enabled,text)))).
Definition main := (@identity,@call,@pack,only,single,@view,invoke).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PYTEST'
from pathlib import Path
seen=set();pure=set()
for line in Path('hash.log').read_text().splitlines():
 parts=line.split();name=parts[2]
 assumptions=set(line.split('  assumes ',1)[1].split(', ')) if '  assumes ' in line else set()
 seen.update(assumptions)
 if name in {'main.identity','main.call','main.pack','main.only','main.single','main.view'}:
  assert not assumptions,(name,assumptions)
  pure.add(name)
assert len(pure)==6,pure
# The separate opaque-callable exercise uses the pre-existing Native.program
# primitive-word carrier. Record construction/projection/matching stays pure.
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PYTEST
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_record_*.ml .
cp native/soma_callable_*.ml .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let old_call value argument=value.Target.callback argument
let ()=
 let name=String.make 1048576 'n' and payload=String.make 1048576 'p' in
 let values=[payload] and seen=ref 0 and fault=Failure "record callback"in
 let callback text=incr seen;if text==name then raise fault;require "borrowed callback argument"(text==payload);text in
 let value=Target.{name;values;callback}in
 require "borrowed record"(Prog.identity value==value);
 require "opaque callable aliases retain labels and borrowed results"(match Prog.invoke (Some false) payload with false,text->text==payload|_->false);
 require "borrowed callback result"(Prog.call value payload==payload);
 require "original callback identity"(match Prog.view value with((n,v),f)->n==name&&v==values&&f==callback);
 require "native constructor borrows all fields"(let p=Prog.pack name values callback in p.Target.name==name&&p.values==values&&p.callback==callback);
 require "exact callback fault"(try ignore(Prog.call value name);false with error->error==fault);
 require "singleton read borrows text"(Prog.only Target.{text=name}==name);
 require "singleton construction uses native record"((Prog.single name).Target.text==name);
 let allocation f=Gc.full_major();let before=Gc.allocated_bytes()in
  for _=1 to 100000 do ignore(Sys.opaque_identity(f value payload))done;Gc.allocated_bytes()-.before in
 require "direct native call allocation"(allocation old_call=allocation Prog.call);
 let weak=Weak.create 1 in
 let consume()=let value=Target.{name=String.make 1024 'x';values=[];callback=(fun text->text)}in
  Weak.set weak 0(Some value);ignore(Prog.call value payload)in
 consume();Gc.full_major();Gc.full_major();require "consumed record released"(not(Weak.check weak 0));
 print_endline "PASS: exact parametric/singleton native records, direct constructors/projections/matches, borrowed fields/results, exact faults and native allocation."
let lifetime call=
 let owner=Weak.create 1 and payload=Weak.create 1 and observed=ref[] in
 let flags()=Weak.check owner 0,Weak.check payload 0 in
 let invoke()=
  let text=String.make 1048576 'l' in
  let value=Target.{name="weak";values=[];callback=(fun _->Gc.full_major();Gc.full_major();observed:=flags() :: !observed;true)} in
  Weak.set owner 0(Some value);Weak.set payload 0(Some text);ignore(call value text)in
 invoke();Gc.full_major();Gc.full_major();List.rev !observed,flags()
let ()=
 require "direct callback preserves record/argument Weak phases"(lifetime old_call=lifetime Prog.call);
 let key=Lwt.new_key()and promise,_=Lwt.task()and calls=ref 0 and canceled=ref 0 in
 Lwt.on_cancel promise(fun()->incr canceled);
 let callback _=incr calls;require "caller Lwt context"(Lwt.get key=Some "caller");promise in
 let value=Lwt.with_value key(Some "creation")(fun()->Target.{name="promise";values=[];callback})in
 let partial=Prog.call value in require "quiet partial application"(!calls=0);
 let actual=Lwt.with_value key(Some "caller")(fun()->partial "argument")in
 require "exact returned promise"(actual==promise);
 Lwt.cancel actual;require "exact cancellation"(!calls=1&& !canceled=1);
 print_endline "PASS: direct record callback Weak phases, partial application, exact promise/cancellation and invocation-time Lwt context."
ML
for compiler in ocamlc ocamlopt;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml \
  target.ml soma_record_*.ml soma_callable_*.ml soma_bindings.ml prog.mli prog.ml check.ml
 "./check-$compiler"
done
# Only a bare original logical type is used: the ABI check must still be emitted.
cat > identity.soma <<'SOMA'
Import target.
Definition identity {A B : Type} (value : producer.entry A B) := value.
Definition main := @identity.
SOMA
for shape in extra missing reordered wrong_type mutable_field;do
 case "$shape" in
 extra) fields="name:string;values:'a list;callback:'a -> 'b;extra:bool";;
 missing) fields="name:string;values:'a list";;
 reordered) fields="values:'a list;name:string;callback:'a -> 'b";;
 wrong_type) fields="name:string;values:'a option;callback:'a -> 'b";;
 mutable_field) fields="mutable name:string;values:'a list;callback:'a -> 'b";;
 esac
 printf "type ('a,'b) entry = { %s }\ntype ('a,'b) nested = { nested_callback : ('a -> 'b) -> 'a -> 'b }\ntype singleton = { text:string }\nlet invoke ?(enabled=true) text=enabled,text\n" "$fields" >target.ml
 soma extract identity.soma -no-soma-prelude -o "$shape" >"$shape.log" 2>&1
 if(cd "$shape"&&dune build --profile release -j2)>>"$shape.log" 2>&1;then
  echo "accepted incompatible native record ABI: $shape" >&2;exit 1
 fi
 grep -Eq 'does not match|field|not compatible|declarations' "$shape.log"
done

cat > implementation.ml <<'ML'
let value=true
ML
cat > implementation.definition <<'SOMA'
From Stdlib Require Import Bool.
Definition value := true.
SOMA
cat > invalid.soma <<'SOMA'
Import implementation.
Definition main := tt.
SOMA
if soma extract invalid.soma -no-soma-prelude -o invalid >invalid.log 2>&1;then
 echo 'accepted a runtime implementation in a foreign definition' >&2;exit 1
fi
grep -q 'defines nothing' invalid.log
