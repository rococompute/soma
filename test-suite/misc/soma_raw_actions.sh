#!/usr/bin/env bash
# write, random_bytes, monotonic_ns, wall_clock, receive, local_address,
# select, watch, after and UDP:
# extraction, which images get a network, the OCaml
# check against the libraries' signatures, and the runtime's conversions
# on fixed inputs. No image, no clock reads.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
export SOMA_MIRAGE_SWITCH=nonexistent
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cd "$WORK"
cp "$ROOT/examples/example_files/mirage_raw_clock/mirage_raw_clock.soma" .
soma build --no-image mirage_raw_clock.soma > raw.log 2>&1
grep -q '(no image)' raw.log
PLAIN="$SOMA_MIRAGE_DIR/plain"
for c in Write Random_bytes Monotonic_ns Wall_clock; do grep -q "$c" "$PLAIN/prog.ml"; done
[ ! -e mirage_raw_clock.hvt ]

# receive and local_address: a network image; local_address, a constructor
# without arguments, is told from its declaration, which every program has
cp "$ROOT/examples/example_files/mirage_raw_link/mirage_raw_link.soma" .
soma build --no-image mirage_raw_link.soma > link.log 2>&1
grep -q 'mirage/net (no image)' link.log
for c in Receive Local_address; do grep -q "$c" "$SOMA_MIRAGE_DIR/net/prog.ml"; done
grep -q 'mirage/plain (no image)' raw.log
cat > address_only.soma <<'SOMA'
Require Import Sandbox.
main : io unit := a <- local_address ;; print (match a with Some s => s | None => "none" end).
SOMA
soma build --no-image address_only.soma > address.log 2>&1
grep -q 'mirage/net (no image)' address.log

# select, watch, after and UDP: timers alone need no network, the rest do
cp "$ROOT/examples/example_files/mirage_events/mirage_events.soma" .
soma build --no-image mirage_events.soma > events.log 2>&1
grep -q 'mirage/net (no image)' events.log
for c in Select Watch After Udp_listen Udp_send Datagram Timer Linked; do grep -q "$c" "$SOMA_MIRAGE_DIR/net/prog.ml"; done
cat > timer_only.soma <<'SOMA'
Require Import Sandbox.
From Stdlib Require Import NArith.
main : io unit := after 10%N 7 ;; got <- select 1000%N ;;
  match got with cons (Timer 7) nil => print "timer" | _ => exit 1 end.
SOMA
soma build --no-image timer_only.soma > timer.log 2>&1
grep -q 'mirage/plain (no image)' timer.log
# the runtime's quiet switch reaches every event
grep -q 'if not (quiet ()) then' "$SOMA_MIRAGE_DIR/plain/soma_rt.ml"

# a nanosecond reading is a primitive int, not a nat
cat > misused.soma <<'SOMA'
Require Import Sandbox.
main : io unit := ns <- monotonic_ns ;; sleep ns.
SOMA
if soma build --no-image misused.soma > misused.log 2>&1; then
    echo 'a nanosecond reading used as a nat passed' >&2
    exit 1
fi
grep -q 'Error' misused.log

# the runtime's conversions, on fixed inputs
cat > helpers.ml <<'OCAML'
OCAML
sed -n '/^let seconds_and_ns /,/^let ns_of_elapsed / p' "$PLAIN/soma_rt.ml" >> helpers.ml
cat >> helpers.ml <<'OCAML'
let () =
  assert (seconds_and_ns (0, 0L) = (0, 0));
  (* 2023-11-14 22:13:20.123456789 UTC: day 19675, 80000.123456789 s in *)
  assert (seconds_and_ns (19675, 80_000_123_456_789_000L) = (1_700_000_000, 123_456_789));
  assert (seconds_and_ns (1, 86_399_999_999_999_999L) = (172_799, 999_999_999));
  assert (ns_of_elapsed 0L = 0);
  assert (ns_of_elapsed 4_000_000_000_000_000_000L = 4_000_000_000_000_000_000);
  (* unsigned nanoseconds past OCaml's int: the top bit dropped, never negative *)
  assert (ns_of_elapsed (-1L) = max_int)
OCAML
ocamlc helpers.ml -o helpers.exe > helpers.log 2>&1
./helpers.exe >> helpers.log 2>&1
