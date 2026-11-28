#!/usr/bin/env bash
# Alias the complete type constructor, including implicit/mixed parameters.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 30 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >producer.soma <<'SOMA'
From Stdlib Require Import Strings.String List.
Record pair {A B : Type} := Pair { name : string; transform : A -> B }.
Record mixed (A : Type) {B : Type} := Mixed { values : list A; consume : A -> B }.
Record single {A : Type} := Single { item : A }.
SOMA
cat >target.ml <<'ML'
type ('a,'b) pair={name:string;transform:'a->'b}
type ('a,'b) mixed={values:'a list;consume:'a->'b}
type 'a single={item:'a}
ML
cat >target.definition <<'SOMA'
From Soma Require Import Native.
Import producer.
OCaml Native Record Alias pair := producer.pair As "Target.pair".
OCaml Native Record Alias mixed := producer.mixed As "Target.mixed".
OCaml Native Record Alias single := producer.single As "Target.single".
Check (pair nat bool).
Check (mixed string nat).
Check (single string).
Fail Check (pair nat bool nat).
Fail Check (single string nat).
SOMA
cat >main.soma <<'SOMA'
From Stdlib Require Import Strings.String List.
Import target.
Definition identity {A B : Type} (value : pair A B) := value.
Definition call {A B : Type} (value : pair A B) argument := producer.transform value argument.
Definition pack {A B : Type} text (body : A -> B) : pair A B := @producer.Pair A B text body.
Definition pack_mixed {A B : Type} items (body : A -> B) : mixed A B := @producer.Mixed A B items body.
Definition unpack_mixed {A B : Type} (value : mixed A B) := (@producer.values A B value,@producer.consume A B value).
Definition pack_single {A : Type} value : single A := @producer.Single A value.
Definition unpack_single {A : Type} (value : single A) := producer.item value.
Definition main := (@identity,@call,@pack,@pack_mixed,@unpack_mixed,@pack_single,@unpack_single).
Verification Properties "cross_module_call" Invariants "" Trust "".
SOMA
cat >main.exp <<'SOMA'
Theorem cross_module_call : forall A B text (body : A -> B) argument,
  call (pack text body) argument = body argument.
Proof. reflexivity. Qed.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
python3 - <<'PY'
from pathlib import Path
import tomllib
r=tomllib.loads(Path('native/verification.toml').read_text())
assert r['used-assumptions']==[]
assert [p['name'] for p in r['properties']]==['cross_module_call']
assert r['properties'][0]['assumptions']==[]
PY
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,prog.ml,prog.mli,soma_bindings.ml,target.ml} .
cp native/soma_record_*.ml .
cat >check.ml <<'ML'
let ()=
 let text=String.make 1048576 'x' and values=[true;false] in
 let error=Failure "implicit record" in
 let body value=if value then text else raise error in
 let pair=Prog.pack text body in
 assert(Prog.identity pair==pair && pair.Target.name==text && pair.Target.transform==body);
 assert(Prog.call pair true==text);
 (try ignore(Prog.call pair false);assert false with observed->assert(observed==error));
 let mixed=Prog.pack_mixed values body in
 let observed,callback=Prog.unpack_mixed mixed in
 assert(observed==values && callback==body && mixed.Target.values==values);
 assert(Prog.unpack_single(Prog.pack_single text)==text);
 assert(Prog.call(Prog.pack "integer"(fun value->value+1))41=42);
 let weak=Weak.create 1 in
 let invoke()=let pair=Prog.pack(String.make 1024 'w')(fun value->value)in
  Weak.set weak 0(Some pair);ignore(Prog.call pair true)in
 invoke();Gc.full_major();Gc.full_major();assert(not(Weak.check weak 0));
 print_endline "PASS: implicit/mixed/single parameterized record aliases, typed Source construction/calls, borrowed identity, faults and Weak release"
ML
for backend in ocamlopt ocamlc; do
 ocamlfind "$backend" -w -a -package lwt -linkpkg soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_record_*.ml soma_bindings.ml prog.mli prog.ml check.ml -o "check-$backend" >"$backend.log" 2>&1
 "./check-$backend"
done
