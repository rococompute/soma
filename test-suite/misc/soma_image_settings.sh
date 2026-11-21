#!/usr/bin/env bash
# soma.toml's [image]: memory and text_start are checked, each wrong one
# saying what to write; an image linked elsewhere has a project of its
# own, named after its address (checked without an image).
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 30 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
export SOMA_MIRAGE_SWITCH=nonexistent
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cd "$WORK"
printf 'Require Import Sandbox.\nmain : io unit := print "high".\n' > main.soma

project() {
    printf '[project]\nname = "high"\nversion = "0.1.0"\n\n[image]\n%s\n' "$1" > soma.toml
}

# refused: SETTINGS MESSAGE
refused() {
    project "$1"
    if soma build --no-image main.soma > refused.log 2>&1; then
        echo "[image] $1 was accepted" >&2; exit 1
    fi
    grep -q "$2" refused.log || { echo "[image] $1: no \"$2\"" >&2; cat refused.log >&2; exit 1; }
}

refused 'memory = "4096"' 'memory is a string; it is the image.s megabytes'
refused 'memory = 0' 'a number from 1 to 1048576'
refused 'text_start = 3221225472' 'text_start is an integer; it is an address, a string'
refused 'text_start = "C0000000"
memory = 4096' 'is no address: 0x and hexadecimal digits'
refused 'text_start = "0xC0000001"
memory = 4096' 'at a multiple of 0x10000'
refused 'text_start = "0x80000"
memory = 4096' 'linked at 0x100000 (1 MB) or above'
refused 'text_start = "0xC0000000"' 'needs memory above it: memory = 3136'
refused 'text_start = "0xC0000000"
memory = 2048' 'is past the image.s 2048 MB of memory'
refused 'stack = 8' 'stack is not a key of \[image\]'
refused 'user_memory = "guest"' 'user_memory is an array'
refused 'user_memory = [{ name = "guest", size = 1 }]' 'size is a positive multiple'
refused 'user_memory = [{ name = "bad-name", size = "0x100000" }]' 'name of 1 to 67'
refused 'user_memory = [{ name = "guest", address = "0x100001", size = "0x100000" }]' 'address is at least'
refused 'user_memory = [{ name = "guest", size = "0x100000" }, { name = "guest", size = "0x100000" }]' 'declared twice'
refused 'user_memory = [{ name = "one", address = "0x200000", size = "0x200000" }, { name = "two", address = "0x300000", size = "0x100000" }]' 'regions.*overlap'
refused 'memory = 4
user_memory = [{ name = "guest", address = "0x200000", size = "0x400000" }]' 'past the image'
refused 'memory = 4096
text_start = "0xC0000000"
user_memory = [{ name = "guest", address = "0x200000", size = "0xC0000000" }]' 'overlaps text_start'

# accepted: memory alone keeps the usual project; text_start has its own
project 'memory = 512'
soma build --no-image main.soma > memory.log 2>&1
grep -q 'mirage/plain (no image)' memory.log
project 'memory = 4096
text_start = "0xC0000000"'
soma build --no-image main.soma > high.log 2>&1
grep -q 'mirage/plain-text-c0000000 (no image)' high.log
grep -q 'register "soma" ~text_start:0xc0000000' "$SOMA_MIRAGE_DIR/plain-text-c0000000/config.ml"
project 'memory = 4096
text_start = "0xC0000000"
user_memory = [{ name = "guest", address = "0x200000", size = "0xbfd00000" }]'
soma build --no-image main.soma > user.log 2>&1
P=$(sed -n 's/^Mirage: checked \(.*\) (no image)$/\1/p' user.log)
grep -q 'user_memory ~address:0x200000 ~size:0xbfd00000 "guest"' "$P/config.ml"
# Changing a manifest region cannot reuse another image's generated project.
project 'memory = 4096
text_start = "0xC0000000"
user_memory = [{ name = "guest", address = "0x200000", size = "0xbfc00000" }]'
soma build --no-image main.soma > other.log 2>&1
Q=$(sed -n 's/^Mirage: checked \(.*\) (no image)$/\1/p' other.log)
[ "$P" != "$Q" ]
echo "image settings: ok"
