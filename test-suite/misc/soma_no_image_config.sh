#!/usr/bin/env bash
# The no-image check parses generated config.ml and type-checks the project.
# An existing Sandbox example passes, with the switch unset and with a
# switch named that is not installed. A program that prints a fetch result
# (fetched, not a string) fails. A config.ml the compiler refuses fails
# with the compiler's message. No solo5 and no MirageOS switch.
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE SOMA_MIRAGE_SWITCH
cd "$WORK"
cp "$ROOT/examples/example_files/mirage_minimal/mirage_minimal.soma" .
# --no-image wins even when a switch is named and not installed
SOMA_MIRAGE_SWITCH=nonexistent soma build --no-image mirage_minimal.soma > good.log 2>&1
grep -q '(no image)' good.log
test -f "$SOMA_MIRAGE_DIR/plain/config.ml"
test -f "$SOMA_MIRAGE_DIR/plain/no-image/config.ml"
test -f "$SOMA_MIRAGE_DIR/plain/no-image/prog.cmo"
test -f "$SOMA_MIRAGE_DIR/plain/no-image/soma_rt.cmo"
cmp -s "$SOMA_MIRAGE_DIR/plain/config.ml" "$SOMA_MIRAGE_DIR/plain/no-image/config.ml"
ocamlc -stop-after parsing -c "$SOMA_MIRAGE_DIR/plain/no-image/config.ml"
test ! -e mirage_minimal.hvt
test ! -e "$SOMA_MIRAGE_DIR/plain/dist/soma.hvt"
# a plain build with the switch unset takes the same path
unset SOMA_MIRAGE_SWITCH
soma build mirage_minimal.soma > fallback.log 2>&1
grep -q '(no image)' fallback.log
test ! -e mirage_minimal.hvt

# the parse is part of the check: a compiler that refuses config.ml fails it
REAL_OCAMLC=$(command -v ocamlc)
export REAL_OCAMLC
mkdir compiler
cat > compiler/ocamlc <<'EOF'
#!/bin/sh
case " $* " in
  *' -stop-after parsing '*)
    echo 'File "config.ml", line 1, characters 0-0:' >&2
    echo 'Error: Syntax error' >&2
    exit 2
    ;;
esac
exec "$REAL_OCAMLC" "$@"
EOF
chmod +x compiler/ocamlc
if PATH="$WORK/compiler:$PATH" SOMA_MIRAGE_SWITCH=nonexistent \
    soma build --no-image mirage_minimal.soma > parse.log 2>&1; then
    echo 'a config.ml parse error passed the Sandbox check' >&2
    exit 1
fi
grep -q 'OCaml check failed' parse.log
grep -q 'config.ml' parse.log
grep -q 'Error:' parse.log
test ! -e mirage_minimal.hvt

# print expects a string; what fetch returns is fetched
cat > illtyped.soma <<'SOMA'
Require Import Sandbox.
main : io unit :=
  r <- fetch "127.0.0.1" 9 (http_get "/") ;;
  print r.
SOMA
if soma build --no-image illtyped.soma > illtyped.log 2>&1; then
    echo 'a fetched value was accepted as a string' >&2
    exit 1
fi
grep -q 'Error' illtyped.log
test ! -e illtyped.hvt
