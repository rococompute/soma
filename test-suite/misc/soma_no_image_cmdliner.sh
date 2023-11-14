#!/usr/bin/env bash
# Argument specifications must be converted to terms before registration,
# just as Mirage_runtime requires in a real image.
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE SOMA_MIRAGE_SWITCH
cd "$WORK"
cp "$ROOT/examples/example_files/mirage_minimal/mirage_minimal.soma" .
soma build --no-image mirage_minimal.soma
REAL_OCAMLC=$(command -v ocamlc)
export REAL_OCAMLC
mkdir compiler
cat > compiler/ocamlc <<'WRAPPER'
#!/bin/sh
case " $* " in
  *' -open Standins '*)
    cat >> soma_rt.ml <<'BROKEN'
let broken =
  Mirage_runtime.register_arg
    (Cmdliner.Arg.flag (Cmdliner.Arg.info ~doc:"Broken" ["broken"]))
BROKEN
    ;;
esac
exec "$REAL_OCAMLC" "$@"
WRAPPER
chmod +x compiler/ocamlc
if PATH="$WORK/compiler:$PATH" soma build --no-image mirage_minimal.soma > broken.log 2>&1; then
    echo 'an argument specification was accepted as a Cmdliner term' >&2
    exit 1
fi
grep -q 'Error:' broken.log
grep -q 'Cmdliner.Arg.t' broken.log
grep -q 'Cmdliner.Term.t' broken.log
