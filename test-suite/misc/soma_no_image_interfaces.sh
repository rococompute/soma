#!/usr/bin/env bash
# Check the remaining example paths and reject network interface mistakes
# without a Mirage switch, a booted guest, or edits to the source tree.
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE SOMA_MIRAGE_SWITCH
mkdir "$WORK/examples"
cd "$WORK/examples"
for name in mirage_hello mirage_supervised mirage_minimal_web_server; do
    cp -R "$ROOT/examples/example_files/$name" .
    soma build --no-image "$name/$name.soma" > "$WORK/$name.log" 2>&1
    grep -q '(no image)' "$WORK/$name.log"
    [ ! -f "$name/$name.hvt" ]
done
# This path compiles soma_wasm.ml against the installed interpreter, in
# addition to checking the Mirage interfaces against the stand-ins.
mkdir wasm
cp "$ROOT/examples/example_projects/wasm_add/"{image.soma,add.definition,add.wasm} wasm/
soma build --no-image wasm/image.soma > "$WORK/wasm.log" 2>&1
grep -q '(no image)' "$WORK/wasm.log"
test -f "$SOMA_MIRAGE_DIR/plain-wasm/no-image/soma_wasm.cmo"
test -f "$SOMA_MIRAGE_DIR/plain-wasm/no-image/prog.cmo"
test -f "$SOMA_MIRAGE_DIR/plain-wasm/no-image/soma_rt.cmo"
[ ! -f wasm/image.hvt ]
# Inject each mistake immediately before compilation. Rebuilding copies a
# fresh unikernel.ml each time, so failures cannot contaminate later cases.
REAL_OCAMLC=$(command -v ocamlc)
export REAL_OCAMLC
mkdir "$WORK/compiler"
cat > "$WORK/compiler/ocamlc" <<'WRAPPER'
#!/bin/sh
case " $* " in
  *' -open Standins '*)
    case "$BROKEN_INTERFACE" in
      flow) expression='S.TCP.read "not a flow"' ;;
      buffer) expression='S.TCP.write flow "not a buffer"' ;;
      address) expression='S.TCP.create_connection (S.tcp stack) ("not an address", 80)' ;;
      promise) expression='(S.TCP.close flow : unit)' ;;
      *) exit 2 ;;
    esac
    printf '\nmodule Broken (S : Tcpip.Stack.V4V6) = struct\nlet broken stack flow = %s\nend\n' "$expression" >> unikernel.ml
    ;;
esac
exec "$REAL_OCAMLC" "$@"
WRAPPER
chmod +x "$WORK/compiler/ocamlc"
for interface in flow buffer address promise; do
    if PATH="$WORK/compiler:$PATH" BROKEN_INTERFACE="$interface" \
        soma build --no-image mirage_minimal_web_server/mirage_minimal_web_server.soma \
        > "$WORK/broken-$interface.log" 2>&1; then
        echo "ill-typed TCP $interface passed the Sandbox check" >&2
        exit 1
    fi
    grep -q 'unikernel.ml' "$WORK/broken-$interface.log"
    grep -q 'Error:' "$WORK/broken-$interface.log"
done
