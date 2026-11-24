#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$root/_build/install/default/bin/soma}
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 50 "$work"/*.log || true; fi; rm -rf "$work"' EXIT
host() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }
cat > "$work/callbacks.soma" <<'SOMA'
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
Definition prepare3 (_ : unit) :=
  Export (lexical_callback3 (fun a b c => Return (PrimInt63.sub (PrimInt63.add a b) c))).
Definition body5 a b c d e := Return (PrimInt63.sub (PrimInt63.add (PrimInt63.add a b) c) (PrimInt63.add d e)).
Definition prepare5 (_ : unit) := Export (lexical_callback5 body5).
Definition prepare6 a :=
  Export (lexical_callback6 (fun b c d e f g =>
    Return (PrimInt63.sub (PrimInt63.add (PrimInt63.add a b) (PrimInt63.add c d))
                        (PrimInt63.add (PrimInt63.add e f) g)))).
Definition prepare_dynamic (f : PrimInt63.int -> PrimInt63.int -> PrimInt63.int -> program PrimInt63.int) :=
  Export (lexical_callback3 f).
Definition main := (prepare3, (prepare5, (prepare6, prepare_dynamic))).
SOMA
"$SOMA" extract "$work/callbacks.soma" -o "$work/native" > "$work/extract.log" 2>&1
cat > "$work/native/probe.ml" <<'ML'
let check label ok = if not ok then failwith label
let[@inline never] original3 () = fun a b c -> a + b - c
let[@inline never] original5 () = fun a b c d e -> a + b + c - (d + e)
let[@inline never] original6 a = fun b c d e f g -> a + b + (c + d) - (e + f + g)
let repeated make v =
  let first = Sys.opaque_identity (make v) in
  let second = Sys.opaque_identity (make v) in
  first == second

let () =
  let prepare3,(prepare5,(prepare6,prepare_dynamic)) = Prog.soma_main () in
  check "closed literal callback identity" (repeated original3 () = repeated prepare3 ());
  check "closed global callback identity" (repeated original5 () = repeated prepare5 ());
  check "capturing callback identity" (repeated original6 7 = repeated prepare6 7);
  check "three arguments" (prepare3 () 13 7 3 = 17);
  check "five arguments" (prepare5 () 13 7 3 9 1 = 13);
  check "six arguments and capture" (prepare6 9 13 7 3 2 1 5 = 24);
  let calls = ref 0 in
  let error = Failure "callback error" in
  let body a b c () = incr calls; if c = 0 then raise error else a + b - c in
  let callback = prepare_dynamic body in
  check "callback is deferred" (!calls = 0);
  check "dynamic callback result" (callback 5 3 1 = 7 && !calls = 1);
  (match callback 3 2 0 with
   | exception got when got == error && !calls = 2 -> ()
   | _ -> failwith "dynamic callback exception");
  print_endline "PASS: lexical callbacks match ordinary closed and capturing OCaml closures"
ML
python3 - "$work/native" <<'PY'
from pathlib import Path
import sys
root = Path(sys.argv[1])
modules = sorted(path.stem for path in root.glob('*.ml') if path.stem != 'soma_main')
(root / 'dune').write_text(
    '(executable (name probe) (modes exe byte) (modules ' + ' '.join(modules)
    + ') (libraries lwt) (flags (:standard -w -a)))\n')
PY
(cd "$work/native" && host dune build --profile release -j2 probe.exe probe.bc) > "$work/build.log" 2>&1
"$work/native/_build/default/probe.exe"
host ocamlrun "$work/native/_build/default/probe.bc"
