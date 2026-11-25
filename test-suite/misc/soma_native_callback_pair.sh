#!/usr/bin/env bash
# Exercise typed mutual callback groups through extraction and both OCaml backends.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'python3 -c "import shutil, sys; shutil.rmtree(sys.argv[1])" "$work"' EXIT
cd "$work"

cat > main.soma <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.

Definition heterogeneous : callback_group (callback nat string * callback string nat) :=
  Export_callback_pair
    (fun _ length n =>
      match n with
      | O => Return "zero"%string
      | S _ => Bind (Call_callback length "borrowed"%string)
          (fun count => Return (if Nat.eqb count 4 then "borrowed"%string else "unexpected"%string))
      end)
    (fun first _ text =>
      Bind (Call_callback first O)
        (fun prefix => Return (if String.eqb text "borrowed"%string
          then String.length prefix else String.length text)))
    (fun first length => Return (first,length)).

Fail Definition invalid : callback_group (callback nat string * callback string nat) :=
  Export_callback_pair (fun _ _ (_ : nat) => Return true)
                       (fun _ _ (_ : string) => Return O)
                       (fun first length => Return (first,length)).

Definition alternating : callback_group (callback PrimInt63.int bool * callback PrimInt63.int bool) :=
  Export_callback_pair
    (fun _ odd n => if PrimInt63.eqb n 0%uint63 then Return true
      else Call_callback odd (PrimInt63.sub n 1%uint63))
    (fun even _ n => if PrimInt63.eqb n 0%uint63 then Return false
      else Call_callback even (PrimInt63.sub n 1%uint63))
    (fun even odd => Return (even,odd)).

Definition saturated :=
  Group_bind (Return "prefix"%string) (fun prefix => Export_callback_pair4
    (fun _ second (_ : unit) (value : string) (limit : nat) (preferred : string) =>
      Bind (Call_callback4 second true value limit tt)
        (fun count => Return (if Nat.eqb count limit then (if String.eqb preferred "prefix"%string then prefix else preferred) else value)))
    (fun first _ (test : bool) (value : string) (limit : nat) (_ : unit) =>
      if test then Return (String.length value)
      else Bind (Call_callback4 first tt value limit ""%string)
             (fun prefix => Return (String.length prefix)))
    (fun first second => Return (first,second))).

Definition main := (heterogeneous,alternating,saturated).
SOMA

soma extract main.soma -no-soma-prelude -o native
(cd native && dune build --profile release -j2)
cp native/{prog.ml,prog.mli,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cat > check.ml <<'OCAML'
let () =
  let text, length = Prog.heterogeneous in
  assert (text 0 = "zero" && text 1 = "borrowed" && length "longer input" = 12);
  let even, odd = Prog.alternating in
  assert (even 500_000 && not (odd 500_000));
  assert (not (even 500_001) && odd 500_001);
  let prefix, count = Prog.saturated in
  assert (prefix () "value" 5 "prefix" = "prefix");
  assert (prefix () "value" 4 "prefix" = "value" && count false "value" 5 () = 0);
  print_endline "PASS: typed mutually recursive native callbacks preserve separate result types and tail calls."
OCAML
for compiler in ocamlc ocamlopt; do
  ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
    soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml \
    prog.mli prog.ml check.ml
  "./check-$compiler"
done

cat > inspect.soma <<'SOMA'
Require Import Soma.Native.
Definition inspect (value : callback_group nat) : nat :=
  match value with
  | Group_bind _ _ => O
  | Export_callback_pair _ _ _ => O
  | Export_callback_pair4 _ _ _ => O
  end.
Definition main := inspect.
SOMA
if soma extract inspect.soma -no-soma-prelude -o inspect > inspect.log 2>&1; then
  echo 'accepted inspection of an executable callback group' >&2; exit 1
fi
grep -q 'cannot be inspected' inspect.log
