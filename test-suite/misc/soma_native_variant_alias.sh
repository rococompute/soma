#!/usr/bin/env bash
# Reuse an existing checked payload sum with an exact, zero-conversion native ABI.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 40 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"' EXIT
cd "$work"
cat > producer.soma <<'SOMA'
From Stdlib Require Import List Strings.String.
Inductive entry := Empty | Selected (name : string) (args : list string).
Inductive recursive := Recursive (next : recursive).
Inductive dependent := Dependent (A : Type) (value : A).
Inductive parameterized (A : Type) := Parameterized (value : A).
Inductive indexed : nat -> Type := Indexed : indexed O.
Inductive evidence : Prop := Evidence.
Definition main := Empty.
SOMA
cat > target.definition <<'SOMA'
From Soma Require Import Native.
Import producer.
OCaml Native Variant Alias entry := producer.entry As "Target.entry".
Fail OCaml Native Variant Alias conflicting := producer.entry As "Other.entry".
Fail OCaml Native Variant Alias recursive := producer.recursive As "Target.recursive".
Fail OCaml Native Variant Alias dependent := producer.dependent As "Target.dependent".
Fail OCaml Native Variant Alias parameterized := producer.parameterized As "Target.parameterized".
Fail OCaml Native Variant Alias indexed := producer.indexed As "Target.indexed".
Fail OCaml Native Variant Alias evidence := producer.evidence As "Target.evidence".
Fail OCaml Native Variant Alias injected := producer.entry As "Target.entry; assert false".
SOMA
printf 'type entry = Empty | Selected of string * string list\n' >target.ml
cat > main.soma <<'SOMA'
From Stdlib Require Import List Strings.String.
Import target.
Import producer.
Definition identity (value : entry) := value.
Definition choose (value : producer.entry) :=
 match value with Empty => None | Selected name args => Some (name,args) end.
Definition pack name args := Selected name args.
Definition main := (identity,choose,pack).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
if grep -q '  assumes ' hash.log; then echo 'payload reuse introduced assumptions' >&2; exit 1; fi
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_enum_*.ml .
cat > check.ml <<'OCAML'
let require text condition=if not condition then failwith text
let original=function Target.Empty->None|Target.Selected(name,args)->Some(name,args)
let () =
 let name=String.make 1048576 'n' and text=String.make 1048576 'a' in
 let args=[text] in let value=Target.Selected(name,args)in
 require "existing variant value is borrowed" (Prog.identity value==value);
 require "nullary native case" (Prog.choose Target.Empty=None);
 require "native payloads are borrowed" (match Prog.choose value with Some(n,a)->n==name && a==args|_->false);
 require "native constructor consumes original payloads" (match Prog.pack name args with Target.Selected(n,a)->n==name && a==args|_->false);
 let allocation f=Gc.full_major();let before=Gc.allocated_bytes()in for _=1 to 100000 do ignore(Sys.opaque_identity(f value))done;Gc.allocated_bytes()-.before in
 let before=allocation original and after=allocation Prog.choose in
 require "direct native match allocation" (before=after);
 print_endline "PASS: exact checked/native payload variant, borrowed value/payload identities and original direct-match allocation."
OCAML
for compiler in ocamlc ocamlopt; do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml \
  target.ml soma_enum_*.ml soma_bindings.ml prog.mli prog.ml check.ml
 "./check-$compiler"
done
cat > identity.soma <<'SOMA'
Import target.
Definition main (value : entry) := value.
SOMA
for shape in extra wrong_type wrong_arity reordered; do
 case "$shape" in
  extra) printf 'type entry = Empty | Selected of string * string list | Extra\n' >target.ml;;
  wrong_type) printf 'type entry = Empty | Selected of string * int list\n' >target.ml;;
  wrong_arity) printf 'type entry = Empty | Selected of (string * string list)\n' >target.ml;;
  reordered) printf 'type entry = Selected of string * string list | Empty\n' >target.ml;;
 esac
 soma extract identity.soma -no-soma-prelude -o "$shape" >"$shape.log" 2>&1
 if (cd "$shape" && dune build --profile release -j2) >>"$shape.log" 2>&1; then
  echo "accepted incompatible native payload ABI: $shape" >&2;exit 1
 fi
 grep -Eq 'does not match|constructor|arity|arities|not compatible' "$shape.log"
done
