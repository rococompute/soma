#!/usr/bin/env bash
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE SOMA_MIRAGE_SWITCH
cp "$ROOT/examples/example_files/mirage_storage_model/mirage_storage_model.soma" "$WORK/"
soma build --no-image "$WORK/mirage_storage_model.soma" > "$WORK/build.log" 2>&1 || {
    cat "$WORK/build.log" >&2
    exit 1
}
grep -q '(no image)' "$WORK/build.log"
test -f "$SOMA_MIRAGE_DIR/plain/no-image/soma_rt.cmo"
