#!/usr/bin/env bash
# Opt-in nat cases preserve bodies/effects and respect custom realizations.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >main.soma <<'SOMA'
From Soma Require Import Native.
Definition branch (get : unit -> nat) (zero : unit -> nat) (positive : nat -> nat) :=
  Native.direct_nat_cases (match get tt with O => zero tt | S before => positive before end).
Definition capture (native_nat_case current : nat) :=
  Native.direct_nat_cases (match current with O => native_nat_case | S native_nat_case => S native_nat_case end).
Definition nested (first second : nat) := Native.direct_nat_cases (match first with
  O => Native.direct_nat_cases (match second with O => 10 | S before => before end)
  | S before => before + second end).
Definition closure (current : nat) := Native.direct_nat_cases (match current with
  O => fun value => value + 10 | S before => fun value => value + before end).
Definition fallback (current : nat) := match current with O => 77 | S before => before end.
Definition native_nat_case (value : nat) := value + 41.
Definition global_capture current := Native.direct_nat_cases (match current with
  O => native_nat_case 7 | S before => native_nat_case before end).
Definition main := (branch, capture, nested, closure, fallback, global_capture).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,prog.ml,prog.mli} .
python3 - <<'PY'
from pathlib import Path
s=Path('prog.ml').read_text()
assert 'if native_nat_case' in s,s
tail=s[s.index('let fallback'):]
assert 'fun fO fS n' in tail,tail
PY
cat >check.ml <<'ML'
let () =
 for current=0 to 100 do
  let calls=ref[] in
  let result=Prog.branch(fun()->calls:="get"::!calls;current)
    (fun()->calls:="zero"::!calls;31)(fun before->calls:="positive"::!calls;before+13)in
  assert(result=(if current=0 then 31 else current-1+13));
  assert(List.rev !calls=(if current=0 then["get";"zero"]else["get";"positive"]));
  assert(Prog.capture 59 current=(if current=0 then 59 else current));
  assert(Prog.fallback current=(if current=0 then 77 else current-1));
  assert(Prog.global_capture current=(if current=0 then 48 else current+40));
  assert(Prog.closure current 7=(if current=0 then 17 else current+6));
  for second=0 to 100 do
   assert(Prog.nested current second=(if current=0 then(if second=0 then 10 else second-1)else current-1+second))
  done
 done;
 let token=Failure(Bytes.to_string(Bytes.of_string "identity"))in
 (try ignore(Prog.branch(fun()->raise token)(fun()->assert false)(fun _->assert false));assert false with e->assert(e==token));
 (try ignore(Prog.branch(fun()->0)(fun()->raise token)(fun _->assert false));assert false with e->assert(e==token));
 print_endline "PASS: opt-in direct nat branches, captures, nested/function results, one scrutinee call, faults and unannotated fallback"
ML
for backend in ocamlopt ocamlc; do
 ocamlfind "$backend" -w -a -package lwt -linkpkg soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml -o "check-$backend" >"$backend.log" 2>&1
 "./check-$backend"
done
cd "$work"
cat >wide.soma <<'SOMA'
From Stdlib Require ExtrOcamlNatInt.
From Soma Require Import Native.
Extract Inductive nat => int64 ["0L" "Int64.succ"]
  "(fun fO fS n -> if n=0L then fO () else fS (Int64.pred n))".
Definition wide_case current := Native.direct_nat_cases (match current with O => 10 | S before => before end).
Definition main := wide_case.
SOMA
soma extract wide.soma -no-soma-prelude -o wide >wide-extract.log 2>&1
mkdir wide-check
cp wide/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,prog.ml,prog.mli} wide-check/
cd wide-check
cat >check.ml <<'ML'
let () = assert(Prog.wide_case 0L=10L && Prog.wide_case 3L=2L);
 print_endline "PASS: a different nat representation retains its own type and eliminator"
ML
for backend in ocamlopt ocamlc; do
 ocamlfind "$backend" -w -a -package lwt -linkpkg soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml -o "check-$backend" >"$work/wide-$backend.log" 2>&1
 "./check-$backend"
done
cat >custom.soma <<'SOMA'
From Stdlib Require ExtrOcamlNatInt.
From Soma Require Import Native.
Extract Inductive nat => int ["0" "Stdlib.Int.succ"]
  "(fun fO fS n -> if n=0 then fO () else fS (n+7))".
Definition custom_case current := Native.direct_nat_cases (match current with O => 10 | S before => before end).
Definition main := custom_case.
SOMA
soma extract custom.soma -no-soma-prelude -o custom >custom-extract.log 2>&1
mkdir custom-check
cp custom/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,prog.ml,prog.mli} custom-check/
cd custom-check
cat >check.ml <<'ML'
let () = assert(Prog.custom_case 0=10 && Prog.custom_case 3=10 && Prog.custom_case 5=12);
 print_endline "PASS: a nonstandard nat eliminator retains its own supplied semantics"
ML
for backend in ocamlopt ocamlc; do
 ocamlfind "$backend" -w -a -package lwt -linkpkg soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml -o "check-$backend" >"$work/custom-$backend.log" 2>&1
 "./check-$backend"
done
