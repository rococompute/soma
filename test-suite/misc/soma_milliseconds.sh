#!/usr/bin/env bash
# Millisecond clock extraction and static typing, without an image or real sleep.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
export SOMA_MIRAGE_SWITCH=nonexistent
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cd "$WORK"
cp "$ROOT/examples/example_files/mirage_milliseconds/mirage_milliseconds.soma" .
soma build --no-image mirage_milliseconds.soma > clock.log 2>&1
grep -q '(no image)' clock.log
PLAIN="$SOMA_MIRAGE_DIR/plain"
test -f "$PLAIN/no-image/prog.cmo"
test -f "$PLAIN/no-image/soma_rt.cmo"
test -f "$PLAIN/no-image/unikernel.cmo"
grep -q 'Monotonic_ms' "$PLAIN/prog.ml"
grep -q 'Sleep_ms' "$PLAIN/prog.ml"
[ ! -e mirage_milliseconds.hvt ]

cat > misused.soma <<'SOMA'
Require Import Sandbox.
main : io unit := ms <- monotonic_ms ;; sleep ms.
SOMA
if soma build --no-image misused.soma > misused.log 2>&1; then
    echo 'a binary millisecond reading used as a unary nat passed' >&2
    exit 1
fi
grep -q 'Error' misused.log

# Execute the generated conversion/sleep helpers on fixed inputs with a
# recording sleep module. No clock reads, delays, or timing races.
cat > helpers.ml <<'OCAML'
module Lwt = struct
  module Infix = struct let ( >>= ) x f = f x end
end
open Lwt.Infix
module Mirage_sleep = struct
  let calls = ref []
  let ns n = assert (n >= 0L); calls := n :: !calls
end
let check x = x
OCAML
sed -n '/^let rec positive_of_int64 /,/^(\* The extracted/ p' "$PLAIN/soma_rt.ml" |
    sed '$d' >> helpers.ml
cat >> helpers.ml <<'OCAML'
let () =
  assert (milliseconds_of_ns 0L = 0L);
  assert (milliseconds_of_ns 999_999L = 0L);
  assert (milliseconds_of_ns 1_000_000L = 1L);
  assert (milliseconds_of_ns 4_294_967_297_999_999L = 4_294_967_297L);
  assert (milliseconds_of_ns Int64.min_int = 9_223_372_036_854L);
  List.iter (fun ms ->
    Mirage_sleep.calls := [];
    sleep_milliseconds (n_of_int64 ms);
    let total = List.fold_left Int64.add 0L !Mirage_sleep.calls in
    assert (total = Int64.mul ms 1_000_000L))
    [0L; 1L; 1000L; 4_294_967_297L];
  (* Just over the largest duration that fits in signed nanoseconds:
     two halves and the odd millisecond, each safely representable. *)
  Mirage_sleep.calls := [];
  sleep_milliseconds (n_of_int64 9_223_372_036_855L);
  assert (List.rev !Mirage_sleep.calls =
    [4_611_686_018_427_000_000L; 4_611_686_018_427_000_000L; 1_000_000L])
OCAML
ocamlc -I "$PLAIN/no-image" "$PLAIN/no-image/prog.cmo" helpers.ml -o helpers.exe > helpers.log 2>&1
./helpers.exe >> helpers.log 2>&1

# Check the new clock contract too: a unit argument is required.
REAL_OCAMLC=$(command -v ocamlc)
export REAL_OCAMLC
mkdir compiler
cat > compiler/ocamlc <<'OCAML'
#!/bin/sh
case " $* " in
  *' -open Standins '*)
    printf '\nlet broken_clock : int64 = Mirage_mtime.elapsed_ns\n' >> soma_rt.ml ;;
esac
exec "$REAL_OCAMLC" "$@"
OCAML
chmod +x compiler/ocamlc
if PATH="$WORK/compiler:$PATH" soma build --no-image mirage_milliseconds.soma > broken.log 2>&1; then
    echo 'a misused monotonic clock passed the OCaml check' >&2
    exit 1
fi
grep -q 'OCaml check failed' broken.log
grep -q 'Error:' broken.log
