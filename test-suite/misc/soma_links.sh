#!/usr/bin/env bash
# Sandbox's links (listen, connect, send, receive_line, close) through
# soma build --no-image: the two link examples type-check, extract and
# generate their network project, and a misused connection operation fails,
# in the Soma program and in the generated OCaml. No solo5 or MirageOS
# switch, nothing booted, nothing timed.
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

# applied NAME FILE: the constructor NAME applied in FILE, its "(" after
# any spaces or line breaks (extraction may break the line between them)
applied() { tr '\n' ' ' < "$2" | grep -Eq "(^|[^A-Za-z0-9_'])$1 +\\("; }

check_built() {
    test -f "$NET/config.ml"
    grep -q stackv4v6 "$NET/config.ml"
    test -f "$NET/no-image/prog.cmo"
    test -f "$NET/no-image/soma_rt.cmo"
    test -f "$NET/no-image/unikernel.cmo"
    [ ! -e "$NET/dist/soma.hvt" ]
    [ ! -e "$SOMA_MIRAGE_DIR/plain/prog.ml" ]
}

# the server: listen, receive_line, send, (close when its handler ends)
cp "$ROOT/examples/example_files/mirage_link_server/mirage_link_server.soma" .
soma build --no-image mirage_link_server.soma > server.log 2>&1
grep -q '(no image)' server.log
[ ! -f mirage_link_server.hvt ]
check_built
# checked now, before the client's build replaces prog.ml
applied Listen "$NET/prog.ml"
grep -q 'Receive_line' "$NET/prog.ml"
applied Send "$NET/prog.ml"

# the client: connect, send, receive_line, close
cp "$ROOT/examples/example_files/mirage_link_client/mirage_link_client.soma" .
soma build --no-image mirage_link_client.soma > client.log 2>&1
grep -q '(no image)' client.log
[ ! -f mirage_link_client.hvt ]
check_built
applied Connect "$NET/prog.ml"
grep -q 'Receive_line' "$NET/prog.ml"

# a connection operation misused in the program: a string is no connection
cat > misused.soma <<'SOMA'
Require Import Sandbox.
main : io unit := s <- send "not a connection" "hello" ;; print "sent".
SOMA
if soma build --no-image misused.soma > misused.log 2>&1; then
    echo 'send on a string passed the check' >&2
    exit 1
fi
grep -q 'Error' misused.log
[ ! -f misused.hvt ]

# a connection operation misused in the generated OCaml, against the
# stand-ins of Mirage's TCP: a line written as a string, not a Cstruct
REAL_OCAMLC=$(command -v ocamlc)
export REAL_OCAMLC
mkdir compiler
cat > compiler/ocamlc <<'EOF'
#!/bin/sh
case " $* " in
  *' -open Standins '*)
    printf '\nmodule Broken (S : Tcpip.Stack.V4V6) = struct\n  let send_line flow = S.TCP.write flow "a line\\n"\nend\n' >> unikernel.ml ;;
esac
exec "$REAL_OCAMLC" "$@"
EOF
chmod +x compiler/ocamlc
cp mirage_link_client.soma broken_client.soma
if PATH="$WORK/compiler:$PATH" soma build --no-image broken_client.soma > broken.log 2>&1; then
    echo 'a misused TCP write passed the Sandbox check' >&2
    exit 1
fi
grep -q 'OCaml check failed' broken.log
grep -q 'unikernel.ml' broken.log
grep -q 'Error:' broken.log
[ ! -f broken_client.hvt ]
