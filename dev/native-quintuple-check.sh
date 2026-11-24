#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$root/_build/install/default/bin/soma}
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 60 "$work"/*.log || true; fi; rm -rf "$work"' EXIT
host() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }

cat > "$work/tuples.definition" <<'SOMA'
From Soma Require Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String.
OCaml Native External Callback load :
  PrimInt63.int -> promise (Native.quintuple PrimInt63.int bool string (list string) (reference string)) :=
  "Host.load".
SOMA
cat > "$work/main.soma" <<'SOMA'
From Soma Require Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Strings.String.
Import tuples.
Definition load_tuple token := Native.Export (Native.Call_callback load token).
Definition rebuild (tuple : Native.quintuple PrimInt63.int bool string (list string) (reference string)) :=
  let 'Native.Quintuple count flag text names marker := tuple in
  Native.Quintuple count flag text names marker.
Definition main := (load_tuple, rebuild).
SOMA
"$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/extract.log" 2>&1

cat > "$work/native/host.ml" <<'ML'
let marker = ref "original"
let names = [String.make 120 'n']
let tuple = (42, true, "data", names, marker)
let pending, wake = Lwt.task ()
let load = function
  | 0 -> pending
  | _ -> Lwt.return tuple
ML
cat > "$work/native/probe.ml" <<'ML'
let check message condition = if not condition then failwith message

let () =
  let pending = Prog.load_tuple 0 in
  check "borrowed promise identity" (pending == Host.pending);
  check "pending phase" (Lwt.is_sleeping pending);
  Lwt.wakeup Host.wake Host.tuple;
  let actual = match Lwt.state pending with Lwt.Return v -> v | _ -> failwith "wake dropped" in
  check "provider tuple identity" (actual == Host.tuple);
  let (count, flag, text, names, marker) = Prog.rebuild actual in
  check "flat destructuring" (count = 42 && flag && text = "data");
  check "field identity" (names == Host.names && marker == Host.marker);
  let ready = Prog.load_tuple 1 in
  check "ready result" (match Lwt.state ready with Lwt.Return v -> v == actual | _ -> false);
  print_endline "PASS: typed native flat five-field tuple, pointer aliases and unchanged promise phases"
ML

configure_probe() {
  python3 - "$work/native" <<'PY'
from pathlib import Path
import sys

root = Path(sys.argv[1])
bindings = (root / 'soma_bindings.ml').read_text()
assert 'Obj.' not in bindings
modules = sorted(p.stem for p in root.glob('*.ml') if p.stem != 'soma_main')
(root / 'dune').write_text(
    '(executable (name probe) (modes exe byte) (modules ' + ' '.join(modules)
    + ') (libraries lwt) (flags (:standard -w -a)))\n'
)
PY
}
configure_probe
(cd "$work/native" && host dune build --profile release -j2 probe.exe probe.bc) > "$work/build.log" 2>&1
"$work/native/_build/default/probe.exe"
host ocamlrun "$work/native/_build/default/probe.bc"

sed -i 's/int bool string/int int string/' "$work/tuples.definition" "$work/main.soma"
"$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/bad-extract.log" 2>&1
configure_probe
if (cd "$work/native" && host dune build --profile release -j2) > "$work/bad-build.log" 2>&1; then
  echo "accepted a bool field as an integer" >&2
  exit 1
fi
grep -q 'soma_bindings.ml' "$work/bad-build.log"
grep -q 'bool' "$work/bad-build.log"
echo 'PASS: incompatible native flat tuple field types rejected'
