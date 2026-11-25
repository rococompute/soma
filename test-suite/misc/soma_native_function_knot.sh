#!/usr/bin/env bash
# Shared prepared views of mutually recursive direct functions are allocated once.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 40 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"' EXIT
cd "$work"
cat > views.ml <<'OCAML'
let preparations=ref 0
let prepared value=incr preparations;value
OCAML
cat > views.definition <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native Callable entry Optional flag :=
 forall (flag : option bool), PrimInt63.int -> string -> unit -> bool.
OCaml Native Wrap AtFullApplication label_entry :
 (option bool -> PrimInt63.int -> string -> unit -> bool) -> entry.
OCaml Native Apply AsFunction call_entry :
 entry -> option bool -> PrimInt63.int -> string -> unit -> bool.
OCaml Native External Value borrow4 : forall A B C D R : Type,
 Native.callback A (Native.callback B (Native.callback C (Native.callback D R))) -> A -> B -> C -> D -> R := "Fun.id".
OCaml Native External Value borrow1 : forall A B : Type, Native.callback A B -> A -> B := "Fun.id".
OCaml Native External Value prepared : forall A : Type, A -> A := "Views.prepared".
OCaml Native Callable group_call := forall R : Type,
 forall (tag : string), (entry -> string -> option bool -> bool) -> Native.function_knot R.
OCaml Native Wrap AtFullApplication label_group : forall R : Type,
 (string -> (entry -> string -> option bool -> bool) -> Native.function_knot R) -> group_call R.

SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
Import views.
Record environment := {
 labelled : views.entry;
 call_second : PrimInt63.int -> string -> option bool -> unit -> bool;
 call_third : string -> PrimInt63.int -> unit -> option bool -> bool;
 call_fourth : unit -> string -> option bool -> PrimInt63.int -> bool;
 call_fifth : option bool -> PrimInt63.int -> string -> unit -> bool
}.
Definition shared_program :=
 Native.Bind (Call_callback (borrow4 (option bool) PrimInt63.int string unit bool) tt) (fun first_raw =>
 Native.Bind (Call_callback (borrow4 PrimInt63.int string (option bool) unit bool) tt) (fun second_raw =>
 Native.Bind (Call_callback (borrow4 string PrimInt63.int unit (option bool) bool) tt) (fun third_raw =>
 Native.Bind (Call_callback (borrow4 unit string (option bool) PrimInt63.int bool) tt) (fun fourth_raw =>
 Native.Bind (Call_callback (borrow4 (option bool) PrimInt63.int string unit bool) tt) (fun fifth_raw =>
 Native.Bind (Call_callback (borrow1 _ _) tt) (fun label_raw =>
 Native.Bind (Call_callback call_entry tt) (fun invoke =>
 Native.Bind (Call_callback (prepared environment) tt) (fun prepared =>
  Native.Return (fun (observe : views.entry -> string -> option bool -> bool) => Export_function_knot5_4
   (fun first second third fourth fifth =>
     let label := label_raw label_entry in
     prepared {|labelled:=label(first_raw first);call_second:=second_raw second;
       call_third:=third_raw third;call_fourth:=fourth_raw fourth;call_fifth:=fifth_raw fifth|})
   (fun e flag n text _ =>
     if PrimInt63.eqb n 0%uint63 then observe (labelled e) text flag
     else call_second e (PrimInt63.sub n 1%uint63) text flag tt)
   (fun e n text flag _ =>
     if PrimInt63.eqb n 0%uint63 then observe (labelled e) text flag
     else call_third e text (PrimInt63.sub n 1%uint63) tt flag)
   (fun e text n _ flag =>
     if PrimInt63.eqb n 0%uint63 then observe (labelled e) text flag
     else call_fourth e tt text flag (PrimInt63.sub n 1%uint63))
   (fun e _ text flag n =>
     if PrimInt63.eqb n 0%uint63 then observe (labelled e) text flag
     else call_fifth e flag (PrimInt63.sub n 1%uint63) text tt)
   (fun e flag n text _ =>
     if PrimInt63.eqb n 0%uint63 then observe (labelled e) text flag
     else invoke (labelled e) flag (PrimInt63.sub n 1%uint63) text tt)
   (fun e => e)))))))))).
Definition shared := Native.Export shared_program.

Definition labelled_shared := Native.Export (Native.Bind shared_program (fun run =>
 Native.Call_callback (label_group environment) (fun (_ : string) observe => run observe))).
Definition main := (shared,labelled_shared).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
python3 - <<'PYTEST'
from pathlib import Path
seen=set()
for line in Path('hash.log').read_text().splitlines():
 if '  assumes ' in line:seen.update(line.split('  assumes ',1)[1].split(', '))
assert seen=={'Corelib.Numbers.Cyclic.Int63.PrimInt63.int'},seen
PYTEST
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/{prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml,views.ml} .
cp native/soma_callable_*.ml .
cat > check.ml <<'OCAML'
let require name condition=if not condition then failwith name
let original observe =
 let rec entry ?flag n text ()=if n=0 then observe entry text flag else second(n-1)text flag()
 and second n text flag ()=if n=0 then observe entry text flag else third text(n-1)()flag
 and third text n () flag=if n=0 then observe entry text flag else fourth()text flag(n-1)
 and fourth () text flag n=if n=0 then observe entry text flag else fifth flag(n-1)text()
 and fifth flag n text ()=if n=0 then observe entry text flag else entry ?flag(n-1)text()in
 entry
let ()=
 let payload=String.make 1048576 'p' and calls=ref 0 and first=ref None in
 let fault=Failure "prepared recursive observer"and failed=ref false in
 let observe entry text flag=
  incr calls;require "borrowed payload"(text==payload);
  (match !first with None->first:=Some entry|Some previous->require "prepared labelled view identity"(previous==entry));
  if !failed then raise fault;Option.value flag ~default:true in
 let env=Prog.labelled_shared ~tag:"typed-native-boundary" observe in
 require "single environment preparation"(!Views.preparations=1);
 let partial=env.Prog.labelled ~flag:false 0 in
 require "partial remains quiet"(!calls=0);
 require "partial fully applied"(not(partial payload())&& !calls=1);
 require "optional default"(env.labelled 0 payload());
 require "same exposed function"(match !first with Some entry->entry==env.labelled|None->false);
 Gc.full_major();let before=Gc.allocated_bytes()in
 require "five-way tail recursion"(env.labelled 1000000 payload());
 require "heterogeneous second argument order"(not(env.call_second 1000000 payload(Some false)()));
 let allocated=Gc.allocated_bytes()-.before in
 require "no per-call tuple or program allocation"(allocated<1024.);
 require "no repeated preparation"(!Views.preparations=1);
 failed:=true;require "exact exception identity"(try ignore(env.labelled 1000 payload());false with error->error==fault);
 Printf.printf "PASS: five heterogeneous recursive functions share one prepared labelled view, borrowed identities, optional/partial timing and direct tail calls (%.0f bytes).\n" allocated;
 let expected=original(fun _ text flag->require "original borrowed payload"(text==payload);Option.value flag ~default:true)in
 require "original/native result"(expected 1000000 payload());
 print_endline "PASS: direct native five-function reference agrees without new logical assumptions."

let make_source observe=(Prog.shared observe).Prog.labelled
type labelled_entry = ?flag:bool -> int -> string -> unit -> bool
type maker = (labelled_entry -> string -> bool option -> bool) -> labelled_entry
let lifetime (make : maker)=
 let entry_weak=Weak.create 1 and payload_weak=Weak.create 1 and owner_weak=Weak.create 1 in
 let flags()=Weak.check entry_weak 0,Weak.check payload_weak 0,Weak.check owner_weak 0 in
 let samples=ref[]in
 let run()=
  let owner=ref(String.make 1048576 'o')in
  let observe _ _ flag=ignore(Sys.opaque_identity !owner);
   Gc.full_major();Gc.full_major();samples:=flags() :: !samples;Option.value flag~default:true in
  let entry=make observe and payload=String.make 1048576 'x'in
  Weak.set entry_weak 0(Some entry);Weak.set payload_weak 0(Some payload);Weak.set owner_weak 0(Some owner);
  ignore(entry 25 payload())in
 run();Gc.full_major();Gc.full_major();List.rev !samples,flags()
let ()=
 let expected=lifetime original and actual=lifetime make_source in
 require "prepared recursion preserves consumed closure/payload/owner Weak stages"(expected=actual);
 require "all consumed recursive owners released after return"(snd actual=(false,false,false));
 let key=Lwt.new_key()in
 let create (make : maker)=Lwt.with_value key(Some "creation")(fun()->make(fun _ _ flag->
   require "direct recursive call observes caller Lwt scope"(Lwt.get key=Some "caller");Option.value flag~default:true))in
 let old=create original and current=create make_source in
 Lwt.with_value key(Some "caller")(fun()->require "caller-scope original"(old 250 "x"());require "caller-scope Source"(current 250 "x"()));
 print_endline "PASS: original/direct prepared recursion has identical consumed closure/payload/owner Weak stages and invocation-time Lwt context."
OCAML
for compiler in ocamlc ocamlopt; do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml \
  views.ml $(ocamldep -sort soma_callable_*.ml) soma_bindings.ml prog.mli prog.ml check.ml
 "./check-$compiler"
done
cat > inspect.soma <<'SOMA'
From Soma Require Import Native.
Definition inspect (value : function_knot nat) : nat :=
 match value with Export_function_knot5_4 _ _ _ _ _ _ _=>O end.
Definition main := inspect.
SOMA
if soma extract inspect.soma -no-soma-prelude -o inspect >inspect.log 2>&1;then
 echo 'accepted native recursive knot inspection' >&2;exit 1
fi
grep -q 'cannot be inspected' inspect.log
