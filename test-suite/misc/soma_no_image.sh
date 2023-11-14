#!/usr/bin/env bash
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cd "$WORK"
for name in mirage_minimal mirage_clock mirage_fetch mirage_http_server; do
    cp "$ROOT/examples/example_files/$name/$name.soma" .
    SOMA_MIRAGE_SWITCH=nonexistent soma build --no-image "$name.soma"
    [ ! -f "$name.hvt" ]
done
for kind in plain net; do
    test -f "$SOMA_MIRAGE_DIR/$kind/config.ml"
    test -f "$SOMA_MIRAGE_DIR/$kind/prog.ml"
    test -f "$SOMA_MIRAGE_DIR/$kind/no-image/prog.cmo"
    test -f "$SOMA_MIRAGE_DIR/$kind/no-image/soma_rt.cmo"
    test -f "$SOMA_MIRAGE_DIR/$kind/no-image/unikernel.cmo"
    [ ! -e "$SOMA_MIRAGE_DIR/$kind/dist/soma.hvt" ]
done
unset SOMA_MIRAGE_SWITCH
soma build -v mirage_minimal.soma > fallback.log 2>&1
grep -q '(no image)' fallback.log
[ ! -f mirage_minimal.hvt ]
# Inject a misuse of a Mirage interface into the generated runtime just
# before OCaml checks it. No source-tree changes, switches or timing races.
REAL_OCAMLC=$(command -v ocamlc)
export REAL_OCAMLC
mkdir compiler
cat > compiler/ocamlc <<'EOF'
#!/bin/sh
case " $* " in
  *' -open Standins '*)
    printf '\nlet broken = Mirage_sleep.ns "not a duration"\n' >> soma_rt.ml ;;
esac
exec "$REAL_OCAMLC" "$@"
EOF
chmod +x compiler/ocamlc
if PATH="$WORK/compiler:$PATH" soma build --no-image mirage_minimal.soma > broken.log 2>&1; then
    echo 'ill-typed runtime passed the Sandbox check' >&2
    exit 1
fi
grep -q 'soma_rt.ml' broken.log
grep -q 'Error:' broken.log
