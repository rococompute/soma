#!/usr/bin/env bash
# Raw labelled invokers preserve saturation and native call frames.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 40 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"' EXIT
cd "$work"
cat > exported.soma <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
Definition poison : Native.entry PrimInt63.int := Native.Export
  (Native.Raise_failure "a type-only export must never run"%string).
SOMA
cat > methods.definition <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
Import exported.
OCaml Native External Value type_identity :
  Native.entry_result poison -> Native.entry_result poison := "Fun.id".
OCaml Native Callable operation Optional scale := forall (R : Type),
  forall (prefix : string) (scale : option PrimInt63.int), string -> R.
OCaml Native Apply AsFunction invoke : forall (R : Type),
  operation R -> string -> option PrimInt63.int -> string -> R.
Fail OCaml Native Apply AsFunction wrong_order : forall (R : Type),
  operation R -> option PrimInt63.int -> string -> string -> R.
Fail OCaml Native Apply AsFunction wrong_result :
  operation string -> string -> option PrimInt63.int -> string -> bool.
Fail OCaml Native Apply AsFunction not_a_callable :
  string -> string -> string.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native Handles.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
Import methods.
Definition immediate := Native.Export (Native.Call_callback (invoke string) tt).
Definition later := Native.Export (Native.Call_callback (invoke (promise string)) tt).
Definition projected := Native.Export (
  Native.Bind (Native.Call_callback type_identity tt) (fun keep =>
    Native.Return (keep 42%uint63))).
Fail Definition wrong_result_type : Native.entry_result exported.poison := true.
Definition main := (immediate,later,projected).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PY'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes ' in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PY
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/{prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cp native/soma_callable_*.ml .
cat > check.ml <<'OCAML'
let require message condition = if not condition then failwith message
let original body prefix scale text = body ~prefix ?scale text
let () =
  require "type-only export projection runs no native initializer" (Prog.projected=42);
  let prefix = String.make 1048576 'p' and payload = String.make 1048576 'v' in
  let calls=ref 0 in
  let body ~prefix:given ?(scale=3) text =
    incr calls;require "prefix is borrowed" (given==prefix);
    if scale=3 then text else given in
  let prepared=Prog.immediate body prefix None in
  require "partial application is quiet" (!calls=0);
  require "default optional argument and result are borrowed" (prepared payload==payload && !calls=1);
  require "explicit optional value uses the same prefix" (Prog.immediate body prefix (Some 7) payload==prefix);
  let allocation call =
    Gc.full_major();let before=Gc.allocated_bytes() in
    for _=1 to 100000 do ignore(call body prefix None payload) done;
    Gc.allocated_bytes()-.before in
  let before=allocation original and after=allocation Prog.immediate in
  require "raw invocation adds no per-call bridge allocation" (after<=before+.512.);
  let key=Lwt.new_key() in
  let pending,_=Lwt.task() in
  let fault=Failure "raw labelled observer" and failed=ref false in
  let asynchronous ~prefix:given ?(scale=3) text =
    require "promise call scope, labels, optional value and aliases"
      (Lwt.get key=Some 41 && given==prefix && text==payload && scale=3);
    if !failed then raise fault else pending in
  Lwt.with_value key (Some 41) (fun () ->
    require "exact pending promise is returned" (Prog.later asynchronous prefix None payload==pending);
    failed:=true;
    require "synchronous fault keeps identity"
      (try ignore(Prog.later asynchronous prefix None payload);false with error->error==fault));
  Lwt.cancel pending;
  require "original promise cancellation is preserved"
    (match Lwt.state pending with Lwt.Fail Lwt.Canceled->true|_->false);
  Printf.printf "PASS: direct native callable labels/defaults/partials, borrowed results, exact faults/promises/context/cancellation and allocation (%.0f/%.0f bytes).\n" before after

let lifetime call =
  let receiver=Weak.create 1 and strings=Weak.create 2 and owner=Weak.create 1 in
  let observations=ref [] in
  let flags()=Weak.check receiver 0,Weak.check strings 0,Weak.check strings 1,Weak.check owner 0 in
  let invoke() =
    let owned=ref(String.make 1048576 'o') in
    let prefix=String.make 1048576 'p' and payload=String.make 1048576 'v' in
    let body ~prefix:_ ?scale:_ _ =
      ignore(Sys.opaque_identity !owned);
      Gc.full_major();observations:=flags() :: !observations;"" in
    Weak.set receiver 0 (Some body);Weak.set owner 0 (Some owned);
    Weak.set strings 0 (Some prefix);Weak.set strings 1 (Some payload);
    ignore(call body prefix None payload) in
  invoke();Gc.full_major();List.rev !observations,flags()
let () =
  let expected=lifetime original and actual=lifetime Prog.immediate in
  require "direct labelled call preserves consumed closure/string/owner Weak phases" (expected=actual);
  require "all consumed call owners are released after return" (snd actual=(false,false,false,false));
  print_endline "PASS: original and generated direct labelled call frames have identical consumed-owner Weak observations."
OCAML
for compiler in ocamlc ocamlopt; do
  ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
    soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml \
    soma_callable_*.ml soma_bindings.ml prog.mli prog.ml check.ml
  "./check-$compiler"
done
