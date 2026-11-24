#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 50 "$WORK"/*.log 2>/dev/null||true;fi;rm -rf "$WORK"' EXIT
ocaml() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }

mkdir "$WORK/app"
cat > "$WORK/app/operators.definition" <<'SOMA'
From Soma Require Native.
From Corelib Require Import PrimInt63 PrimFloat.
OCaml Native External Callback structural : forall (A : Type), A -> A -> bool := "Stdlib.(=)".
OCaml Native External Value physical : forall (A : Type), A -> A -> bool := "Stdlib.( == )".
OCaml Native External Value array_get :
  forall (A : Type), Native.vector A -> PrimInt63.int -> A := "Array.get".
OCaml Native External Callback multiply : PrimInt63.int -> PrimInt63.int -> PrimInt63.int := "Stdlib.(*)".
OCaml Native External Callback sum_float : PrimFloat.float -> PrimFloat.float -> PrimFloat.float := "Stdlib.(+.)".
SOMA
cat > "$WORK/app/main.soma" <<'SOMA'
From Soma Require Native.
From Corelib Require Import PrimInt63.
Import operators.
Definition equal {A} (left right : A) :=
  Native.Export (Native.Call_callback (structural A) (left, right)).
Definition identical {A} (left right : A) :=
  Native.Export (Native.Bind (Native.Call_callback (physical A) tt)
    (fun same => Native.Return (same left right))).
Definition get {A} (values : Native.vector A) index :=
  Native.Export (Native.Bind (Native.Call_callback (array_get A) tt)
    (fun lookup => Native.Return (lookup values index))).
Definition product left right := Native.Export (Native.Call_callback multiply (left, right)).
Definition add_float left right := Native.Export (Native.Call_callback sum_float (left, right)).
Inductive state := Step (remaining : PrimInt63.int) | Done (value : PrimInt63.int).
Definition step (current : state) := match current with
 | Step n => if PrimInt63.eqb n 0%uint63 then Done n else Step (PrimInt63.sub n 1%uint63)
 | Done _ => current
 end.
Definition finish (current : state) := match current with Done n => Some n | Step _ => None end.
Definition run n := Native.Export (Native.loop_values step finish (Step n)).
Definition loop {S A} (step : S -> S) (finish : S -> option A) initial :=
  Native.Export (Native.loop_values step finish initial).
Definition then_loop {S A B} (step : S -> S) (finish : S -> option A) initial (next : A -> B) :=
  Native.Export (Native.loop_values_then step finish initial (fun value => Native.Return (next value))).
Definition main := (@equal, @identical, @get, product, add_float, step, run, @loop, @then_loop).
SOMA
cat > "$WORK/app/main.exp" <<'SOMA'
Theorem fused_value_loop_is_symbolic_bind : forall S A B
    (step : S -> S) (finish : S -> option A) initial (next : A -> Native.program B),
  Native.loop_values_then step finish initial next =
  Native.Bind (Native.loop_values step finish initial) next.
Proof. reflexivity. Qed.
SOMA
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
python3 - "$WORK" <<'PY'
from pathlib import Path
import sys
root = Path(sys.argv[1])
bindings = (root / 'native/soma_bindings.ml').read_text()
assert 'Obj.' not in bindings
for operator in ['=', '==', '*', '+.']:
    assert f'Stdlib.( {operator} )' in bindings
assumed = {name for line in (root / 'hash').read_text().splitlines() if '  assumes ' in line
           for name in line.split('  assumes ', 1)[1].split(', ')}
assert assumed == {
    'Corelib.Numbers.Cyclic.Int63.PrimInt63.int',
    'Corelib.Floats.PrimFloat.float',
}, assumed
PY

cat > "$WORK/native/probe.ml" <<'ML'
let require message valid = if not valid then failwith message

let capture f = try Ok (f ()) with e -> Error e

type scope_state = Hold of unit ref | Observe of (unit -> bool) | Settled of bool

let[@inline never] scoped run =
  let slot = Weak.create 1 in
  let[@inline never] initial () =
    let owner = ref () in
    Weak.set slot 0 (Some owner);
    Hold owner in
  let step = function
    | Hold _ -> Observe (fun () -> Gc.full_major (); Gc.full_major (); Weak.check slot 0)
    | Observe inspect -> Settled (inspect ())
    | Settled _ -> assert false in
  let finish = function Settled value -> Some value | _ -> None in
  run step finish (initial ()) Fun.id

let direct_scope step finish initial next =
  let rec loop state = match finish state with
    | Some result -> next result
    | None -> loop (step state) in
  loop initial

let () =
  let a = Bytes.to_string (Bytes.of_string "repeated key") in
  let b = Bytes.to_string (Bytes.of_string "repeated key") in
  require "polymorphic structural equality" (Prog.equal a b && not (Prog.equal nan nan));
  require "polymorphic reference equality" (Prog.identical a a && not (Prog.identical a b));
  require "raw polymorphic getter" (Prog.get [| a; b |] 0 == a && Prog.get [| 9 |] 0 = 9);
  let fn x = x in
  (match capture (fun () -> Prog.equal fn fn) with
   | Error (Invalid_argument "compare: functional value") -> ()
   | _ -> failwith "functional values must retain structural-equality failure");
  require "star operator parses and runs" (Prog.product (-41) 9 = -369);
  require "operator containing a dot remains qualified" (Prog.add_float 0.25 1.5 = 1.75);
  let trace = ref [] and value = ref 37 in
  let step n = trace := ("step", n) :: !trace; n + 1 in
  let finish n = trace := ("finish", n) :: !trace; if n = 2 then Some value else None in
  require "terminal alias" (Prog.loop step finish 0 == value);
  require "finish before step and never step terminal state"
    (List.rev !trace = ["finish", 0; "step", 0; "finish", 1; "step", 1; "finish", 2]);
  let error = Failure "loop provider" in
  let throws f = match capture f with Error got -> got == error | Ok _ -> false in
  trace := [];
  require "value loop continuation retains terminal alias"
    (Prog.then_loop step finish 0 (fun result -> trace := ("next", !result) :: !trace; result) == value);
  require "finish, step, and continuation order"
    (List.rev !trace = ["finish", 0; "step", 0; "finish", 1; "step", 1; "finish", 2; "next", 37]);
  require "value loop continuation exception from outside the loop"
    (throws (fun () -> Prog.then_loop step finish 0 (fun _ -> raise error)));
  require "fused terminal-provider exception identity"
    (throws (fun () -> Prog.then_loop (fun _ -> assert false) (fun _ -> raise error) 0 Fun.id));
  require "fused step exception identity"
    (throws (fun () -> Prog.then_loop (fun _ -> raise error) (fun _ -> None) 0 Fun.id));
  let old_scope = scoped direct_scope in
  require "fused value loop has the caller's Weak scope" (scoped Prog.then_loop = old_scope);
  if Sys.backend_type = Sys.Native then
    require "ordinary native loop should release its consumed initial value" (not old_scope);
  require "terminal-provider exception identity"
    (throws (fun () -> Prog.loop (fun _ -> assert false) (fun _ -> raise error) 0));
  require "step-provider exception identity"
    (throws (fun () -> Prog.loop (fun _ -> raise error) (fun _ -> None) 0));
  let direct n =
    let rec loop = function Prog.Done n -> n | Prog.Step _ as s -> loop (Prog.step s) in
    loop (Prog.Step n) in
  let measure fn =
    Gc.full_major ();
    let before = Gc.allocated_bytes () in
    let result = fn 200000 in
    Gc.allocated_bytes () -. before, result in
  let fused n = Prog.then_loop Prog.step
      (function Prog.Done value -> Some value | Prog.Step _ -> None)
      (Prog.Step n) Fun.id in
  let old, expected = measure direct and fresh, actual = measure Prog.run in
  let fused_bytes, result = measure fused in
  require "fused value loop result" (result = expected);
  require "fused value loop adds no per-transition allocation" (fused_bytes -. old < 4096.);
  require "unbounded loop result" (actual = expected);
  require "native loop adds no per-transition allocation" (fresh -. old < 4096.);
  Printf.printf "PASS: exact qualified operators and native value loops (direct %.0f B, generated %.0f B, fused %.0f B)\n"
    old fresh fused_bytes
ML
python3 - "$WORK/native" <<'PY'
from pathlib import Path
import sys
root = Path(sys.argv[1])
mods = sorted(p.stem for p in root.glob('*.ml') if p.stem != 'soma_main')
(root / 'dune').write_text('(executable (name probe) (modes exe byte) (modules ' + ' '.join(mods)
    + ') (libraries lwt) (flags (:standard -w -a)))\n')
PY
(cd "$WORK/native" && ocaml dune build --profile release -j2 probe.exe probe.bc) > "$WORK/build.log" 2>&1
"$WORK/native/_build/default/probe.exe"
ocaml ocamlrun "$WORK/native/_build/default/probe.bc"

negative() {
  local name=$1 destination=$2 diagnostic=$3
  mkdir "$WORK/$name"
  printf 'From Soma Require Native.\n%s\n' "$destination" > "$WORK/$name/bad.definition"
  printf 'Import bad.\nDefinition main := tt.\n' > "$WORK/$name/main.soma"
  if "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/native" > "$WORK/$name.log" 2>&1; then
    echo "accepted malformed external reference $name" >&2
    exit 1
  fi
  grep -q "$diagnostic" "$WORK/$name.log"
}
negative unqualified 'OCaml Native External Callback invalid : bool -> bool := "(=)".' 'needs a qualified OCaml operator path'
negative module 'OCaml Native External Callback invalid : bool -> bool := "stdlib.(=)".' 'needs a qualified OCaml operator path'
negative comment 'OCaml Native External Callback invalid : bool -> bool := "Stdlib.(=) (* arbitrary code *)".' 'needs a qualified OCaml operator path'
negative paths 'OCaml Native External Callback invalid : bool -> bool := "Stdlib.( = ; Failure )".' 'needs a qualified OCaml operator path'
negative paren 'OCaml Native External Callback invalid : bool -> bool := "Stdlib.((=))".' 'needs a qualified OCaml operator path'
negative invalid_symbol 'OCaml Native External Callback invalid : bool -> bool := "Stdlib.(->)".' 'needs a qualified OCaml operator path'
negative type_path 'OCaml Native External Type invalid := "Stdlib.(=)".' 'cannot name'
negative proof_parameter 'OCaml Native External Value invalid : forall (P : Prop), P -> P := "Fun.id".' 'type parameters must be named Type or Set'
echo 'PASS: malformed native operator values and type paths rejected'

mkdir "$WORK/wrong_result"
cat > "$WORK/wrong_result/operators.definition" <<'SOMA'
From Soma Require Native.
OCaml Native External Callback wrong : string -> string -> string := "Stdlib.(=)".
SOMA
cat > "$WORK/wrong_result/main.soma" <<'SOMA'
From Soma Require Native.
Import operators.
Definition main := Native.Export (Native.Call_callback wrong ("a", "b")).
SOMA
"$SOMA" extract "$WORK/wrong_result/main.soma" -o "$WORK/wrong_result/native" > "$WORK/wrong_result.log" 2>&1
if (cd "$WORK/wrong_result/native" && ocaml dune build --profile release -j2) >> "$WORK/wrong_result.log" 2>&1; then
  echo "accepted a native equality descriptor returning string" >&2
  exit 1
fi
grep -q 'bool' "$WORK/wrong_result.log"
echo 'PASS: the native compiler checks the declared operator result type'
