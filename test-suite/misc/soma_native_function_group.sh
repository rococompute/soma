#!/usr/bin/env bash
# Direct typed recursive closures must keep native arity and avoid per-call thunks.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'python3 -c "import shutil, sys; shutil.rmtree(sys.argv[1])" "$work"' EXIT
cd "$work"
cat > borrowed.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native External Value borrow3 : forall (A B C R : Type),
  Native.callback A (Native.callback B (Native.callback C R)) -> A -> B -> C -> R := "Fun.id".
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
Import borrowed.
Definition alternating (observe : PrimInt63.int -> string -> bool -> bool) :=
  Function_group_bind (Call_callback (borrow3 PrimInt63.int string bool bool) tt) (fun as_first =>
  Function_group_bind (Call_callback (borrow3 PrimInt63.int bool string bool) tt) (fun as_second =>
    Export_function_pair3
      (fun _ second n payload flag =>
        let other := as_second second in
        if PrimInt63.eqb n 0%uint63 then observe n payload flag
        else other (PrimInt63.sub n 1%uint63) flag payload)
      (fun first _ n flag payload =>
        let other := as_first first in
        if PrimInt63.eqb n 0%uint63 then negb (observe n payload flag)
        else other (PrimInt63.sub n 1%uint63) payload flag)
      (fun first second => (first,second)))).
Fail Definition invalid : function_group (callback nat (callback string (callback bool nat))) :=
  Export_function_pair3 (fun _ _ (n : nat) (_ : string) (_ : bool) => true)
                       (fun _ _ (n : nat) (_ : string) (_ : bool) => n)
                       (fun first _ => first).
Definition main := alternating.
SOMA
soma extract main.soma -no-soma-prelude -o native
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes ' in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PY
(cd native && dune build --profile release -j2)
cp native/{prog.ml,prog.mli,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_bindings.ml .
cat > check.ml <<'OCAML'
let () =
  let payload = String.make 1048576 'x' in
  let calls = ref 0 in
  let fault = Failure "direct recursive observer" in
  let failed = ref false in
  let observe _ text flag =
    incr calls; assert (text == payload);
    if !failed then raise fault;
    flag
  in
  let even, odd = Prog.alternating observe in
  let partial = even 0 payload in
  assert (!calls = 0);
  assert (partial true && !calls = 1);
  assert (not (odd 0 true payload));
  Gc.full_major ();
  let before = Gc.allocated_bytes () in
  assert (even 500000 payload true);
  assert (not (even 500001 payload true));
  assert (not (odd 500000 true payload));
  assert (odd 500001 true payload);
  let allocated = Gc.allocated_bytes () -. before in
  Printf.printf "direct group recursive allocation %.0f bytes\n%!" allocated;
  assert (allocated < 1024.);
  failed := true;
  assert (try ignore (even 1000 payload true); false with error -> error == fault);
  Printf.printf "PASS: direct recursive functions preserve heterogeneous argument order, partial application, borrowed identity, exact faults and tail calls (%.0f bytes).\n" allocated
OCAML
for compiler in ocamlc ocamlopt; do
  ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
    soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml \
    soma_bindings.ml prog.mli prog.ml check.ml
  "./check-$compiler"
done
cat > inspect.soma <<'SOMA'
Require Import Soma.Native.
Definition inspect (value : function_group nat) : nat :=
  match value with
  | Function_group_bind _ _ => O
  | Export_function_pair3 _ _ _ => O
  end.
Definition main := inspect.
SOMA
if soma extract inspect.soma -no-soma-prelude -o inspect >inspect.log 2>&1; then
  echo 'accepted inspection of an executable function group' >&2; exit 1
fi
grep -q 'cannot be inspected' inspect.log
