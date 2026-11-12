#!/usr/bin/env bash
# soma build --no-image with no ocamlc on PATH checks the Sandbox program
# in the opam switch soma build compiles OCaml programs in
# (SOMA_OCAML_SWITCH here), as a CI image whose only OCaml is that switch
# has it; with no switch either, the error says what to do.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
command -v opam >/dev/null || { echo "no opam here: nothing to check"; exit 0; }
switch=$(opam switch show 2>/dev/null) || { echo "no current opam switch: nothing to check"; exit 0; }
opam exec --switch="$switch" -- sh -c 'command -v ocamlc' >/dev/null \
  || { echo "the current switch has no ocamlc: nothing to check"; exit 0; }
# a PATH with soma, opam alone (its own directory may hold an OCaml) and
# the system's tools, and no OCaml
mkdir "$WORK/opam-only"
ln -s "$(command -v opam)" "$WORK/opam-only/opam"
bare="$BIN:$WORK/opam-only:/usr/bin:/bin"
if PATH="$bare" sh -c 'command -v ocamlc' >/dev/null; then
  echo "ocamlc is in /usr/bin or /bin here: it can't be left off PATH"; exit 0
fi
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cd "$WORK"
cp "$ROOT/examples/example_files/mirage_minimal/mirage_minimal.soma" .
PATH="$bare" SOMA_OCAML_SWITCH="$switch" SOMA_MIRAGE_SWITCH=nonexistent \
  soma build --no-image mirage_minimal.soma > ok.log 2>&1 || { cat ok.log; exit 1; }
grep -q '(no image)' ok.log
test -f "$SOMA_MIRAGE_DIR/plain/no-image/prog.cmo"
if PATH="$bare" SOMA_OCAML_SWITCH= XDG_CACHE_HOME="$WORK/empty-cache" SOMA_MIRAGE_SWITCH=nonexistent \
    soma build --no-image mirage_minimal.soma > none.log 2>&1; then
  echo 'no ocamlc and no switch, and the check passed' >&2; exit 1
fi
grep -q 'no ocamlc to check' none.log
grep -q 'SOMA_OCAML_SWITCH' none.log
echo 'ok: --no-image checks in the OCaml switch when PATH has no ocamlc, and says what to do with neither'
