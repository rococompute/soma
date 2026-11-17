#!/bin/sh
# Build and boot native OCaml modules plus Digestif's C-backed SHA-256.
# Requires the hvf/Mirage toolchain; no browser, WASM or network device.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
SWITCH=${SOMA_MIRAGE_SWITCH:-hvf}
WORK=$(mktemp -d "${TMPDIR:-/tmp}/ocaml-mirage-check.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
# Build a copy so the example repository remains free of generated images.
cp -R "$HERE/examples/example_projects/native_crypto" "$WORK/app"
export SOMA_MIRAGE_SWITCH=$SWITCH
export SOMA_MIRAGE_DIR=${SOMA_MIRAGE_DIR:-$WORK/mirage}
if [ "${1:-}" = --no-image ]; then
  "$SOMA" build --no-image "$WORK/app/main.soma" > "$WORK/build.log" 2>&1 || {
    cat "$WORK/build.log"; exit 1;
  }
  echo 'PASS native bindings checked against real Digestif and Lwt interfaces'
  exit 0
fi
"$SOMA" build "$WORK/app/main.soma" > "$WORK/build.log" 2>&1 || {
  cat "$WORK/build.log"; exit 1;
}
timeout 60 opam exec --switch="$SWITCH" -- solo5-hvt --mem=256 -- \
  "$WORK/app/main.hvt" > "$WORK/run.log" 2>&1 || {
  cat "$WORK/run.log"; exit 1;
}
for line in 'native OCaml' '42' \
  'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855' \
  'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad' \
  'native crypto checks passed'; do
  grep -Fx "$line" "$WORK/run.log" || { cat "$WORK/run.log"; exit 1; }
done
# A second checkout must reuse the same dependency project, including
# its exact Digestif version, while rebuilding the application sources.
cp -R "$HERE/examples/example_projects/native_crypto" "$WORK/relocated"
"$SOMA" build "$WORK/relocated/main.soma" > "$WORK/relocated.log" 2>&1 || {
  cat "$WORK/relocated.log"; exit 1;
}
if grep -q 'setting up the MirageOS project' "$WORK/relocated.log"; then
  cat "$WORK/relocated.log"
  echo 'FAIL relocating the program rebuilt its dependency monorepo'; exit 1
fi
echo 'PASS native OCaml and C-backed crypto booted in Solo5'
