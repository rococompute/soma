#!/usr/bin/env bash
# write, random_bytes, monotonic_ns, wall_clock, receive, local_address,
# select, watch, after, UDP, disks, spawn and cells:
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
grep -q 'mirage/net-web (no image)' link.log   # it connects: a name is looked up
for c in Receive Local_address; do grep -q "$c" "$SOMA_MIRAGE_DIR/net-web/prog.ml"; done
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
grep -q 'mirage/net-web (no image)' events.log   # it connects
for c in Select Watch After Udp_listen Udp_send Datagram Timer Linked; do grep -q "$c" "$SOMA_MIRAGE_DIR/net-web/prog.ml"; done
cat > timer_only.soma <<'SOMA'
Require Import Sandbox.
From Stdlib Require Import NArith.
main : io unit := after 10%N 7 ;; got <- select 1000%N ;;
  match got with cons (Timer 7) nil => print "timer" | _ => exit 1 end.
SOMA
soma build --no-image timer_only.soma > timer.log 2>&1
grep -q 'mirage/plain (no image)' timer.log
# disks by name: each literal a block device of the image, the project
# named after them, sorted; a computed name or a bad one is refused
cp "$ROOT/examples/example_files/mirage_disk/mirage_disk.soma" .
soma build --no-image mirage_disk.soma > disk.log 2>&1
grep -q 'mirage/plain-disk-data (no image)' disk.log
grep -q 'block_of_file "data"' "$SOMA_MIRAGE_DIR/plain-disk-data/config.ml"
grep -q 'install_disk "data"' "$SOMA_MIRAGE_DIR/plain-disk-data/unikernel.ml"
cat > disks.soma <<'SOMA'
Require Import Sandbox.
main : io unit :=
  a <- local_address ;; f <- read_file "x" ;; r <- disk_read "rootfs" 0 1 ;; d <- disk_info "data" ;;
  _ <- disk_write "rootfs" 1 "" ;; print "ok".
SOMA
soma build --no-image disks.soma > disks.log 2>&1
D="$SOMA_MIRAGE_DIR/net-storage-disk-data-disk-rootfs"
grep -q "$D (no image)" disks.log
[ "$(grep -c 'package "mirage-block"' "$D/config.ml")" -eq 1 ]
grep -q 'register "soma" \[ main \$ stack \$ storage \$ disk_0 \$ disk_1 \]' "$D/config.ml"
cat > computed.soma <<'SOMA'
Require Import Sandbox.
disk := "rootfs".
main : io unit := r <- disk_read disk 0 1 ;; print "ok".
SOMA
if soma build --no-image computed.soma > computed.log 2>&1; then
    echo 'a computed disk name passed' >&2; exit 1
fi
grep -q 'not a string literal' computed.log
i=0
for bad in root-fs storage; do
    i=$((i + 1))
    printf 'Require Import Sandbox.\nmain : io unit := r <- disk_info "%s" ;; print "ok".\n' "$bad" > "bad$i.soma"
    if soma build --no-image "bad$i.soma" > "bad$i.log" 2>&1; then
        echo "the disk name $bad passed" >&2; exit 1
    fi
    grep -q 'disk name' "bad$i.log"
done

# spawn and cells: no network; a cell keeps its type
cp "$ROOT/examples/example_files/mirage_tasks/mirage_tasks.soma" .
soma build --no-image mirage_tasks.soma > tasks.log 2>&1
grep -q 'mirage/plain (no image)' tasks.log
for c in Spawn New_cell Read_cell Modify_cell; do grep -q "$c" "$SOMA_MIRAGE_DIR/plain/prog.ml"; done
cat > celltype.soma <<'SOMA'
Require Import Sandbox.
main : io unit := c <- new_cell 0 ;; write_cell c "zero".
SOMA
if soma build --no-image celltype.soma > celltype.log 2>&1; then
    echo 'a string written to a cell of nat passed' >&2; exit 1
fi
grep -q 'Error' celltype.log

# fork and await: no network; a task's result keeps its type
cp "$ROOT/examples/example_files/mirage_await/mirage_await.soma" .
soma build --no-image mirage_await.soma > await.log 2>&1
grep -q 'mirage/plain (no image)' await.log
for c in Fork Await Await_within; do grep -q "$c" "$SOMA_MIRAGE_DIR/plain/prog.ml"; done
cat > awaittype.soma <<'SOMA'
Require Import Sandbox.
main : io unit := t <- fork (ret 3) ;; r <- await t ;;
  match r with Completed s => print s | TaskFailed why => print why end.
SOMA
if soma build --no-image awaittype.soma > awaittype.log 2>&1; then
    echo 'a task of nat awaited as a string passed' >&2; exit 1
fi
grep -q 'Error' awaittype.log

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
