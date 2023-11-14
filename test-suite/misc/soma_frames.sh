#!/usr/bin/env bash
# Sandbox's length-prefixed frames (receive_frame, send_frame) through
# soma build --no-image: the two frame examples, a server and a client
# that exchange frames over one connection, type-check, extract and
# generate their network project, whose OCaml types against the stand-ins
# of Mirage's TCP; and programs that misuse a connection's results fail.
# No solo5 or MirageOS switch, nothing booted, nothing timed. The framing
# itself (lines and frames out of chunks) is checked by Sandbox.v's
# Examples and theorems when Soma is built.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
export SOMA_MIRAGE_SWITCH=nonexistent
NET="$SOMA_MIRAGE_DIR/net"
cd "$WORK"

check_built() {
    test -f "$NET/config.ml"
    grep -q stackv4v6 "$NET/config.ml"
    test -f "$NET/no-image/prog.cmo"
    test -f "$NET/no-image/soma_rt.cmo"
    test -f "$NET/no-image/unikernel.cmo"
    [ ! -e "$NET/dist/soma.hvt" ]
    grep -q 'receive_frame' "$NET/unikernel.ml"
    grep -q 'Lwt.choose' "$NET/unikernel.ml"
}

# the server: listen, receive_frame, send_frame
cp "$ROOT/examples/example_files/mirage_frame_server/mirage_frame_server.soma" .
soma build --no-image mirage_frame_server.soma > server.log 2>&1
grep -q '(no image)' server.log
[ ! -f mirage_frame_server.hvt ]
check_built
grep -q 'Listen (' "$NET/prog.ml"
grep -q 'Receive_frame' "$NET/prog.ml"

# the client: connect, send_frame, receive_frame, close
cp "$ROOT/examples/example_files/mirage_frame_client/mirage_frame_client.soma" .
soma build --no-image mirage_frame_client.soma > client.log 2>&1
grep -q '(no image)' client.log
[ ! -f mirage_frame_client.hvt ]
check_built
grep -q 'Connect (' "$NET/prog.ml"
grep -q 'Receive_frame' "$NET/prog.ml"

# fails: soma build --no-image NAME must refuse the program in NAME.soma
refused() {
    if soma build --no-image "$1.soma" > "$1.log" 2>&1; then
        echo "$1 passed the check" >&2
        exit 1
    fi
    grep -q 'Error' "$1.log"
    [ ! -f "$1.hvt" ]
}

# a receive's result used as plain bytes: it is a framed, not a string
cat > frame_as_bytes.soma <<'SOMA'
Require Import Sandbox.
talk (c : connection) : io unit := r <- receive_frame c 5 ;; print r.
main : io unit := listen 7001 talk.
SOMA
refused frame_as_bytes

# what connect gives used as a connection: it is a connected
cat > connected_as_connection.soma <<'SOMA'
Require Import Sandbox.
main : io unit := c <- connect "127.0.0.1" 7001 ;; s <- send_frame c "hi" ;; ret tt.
SOMA
refused connected_as_connection

# a frame received with no time limit given
cat > frame_without_seconds.soma <<'SOMA'
Require Import Sandbox.
talk (c : connection) : io unit :=
  r <- receive_frame c ;;
  match r with Frame d => print d | _ => ret tt end.
main : io unit := listen 7001 talk.
SOMA
refused frame_without_seconds
