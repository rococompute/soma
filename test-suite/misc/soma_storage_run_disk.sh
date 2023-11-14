#!/usr/bin/env bash
# soma run gives a program that keeps files the disk its build names
# (--block:storage=storage.img): created zeroed the first time, in the
# current directory, and kept for the next run. No MirageOS switch: a
# stand-in opam runs the build's commands with stand-in mirage and make, and
# a stand-in solo5-hvt that counts its boots in the disk's first bytes.
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
mkdir "$WORK/fake" "$WORK/run"
cat > "$WORK/fake/opam" <<'SH'
#!/bin/sh
# opam exec --switch=S -- COMMAND...
[ "$1" = exec ] || exit 2
shift
while [ "$1" != "--" ]; do shift; done
shift
exec "$@"
SH
cat > "$WORK/fake/mirage" <<'SH'
#!/bin/sh
exit 0
SH
cat > "$WORK/fake/make" <<'SH'
#!/bin/sh
if [ "$1" = build ]; then mkdir -p dist && : > dist/soma.hvt; fi
SH
cat > "$WORK/fake/solo5-hvt" <<'SH'
#!/bin/sh
disk=""
for a in "$@"; do
  case "$a" in --block:storage=*) disk="${a#--block:storage=}" ;; esac
done
[ -n "$disk" ] || { echo "no storage disk given"; exit 3; }
[ "$(wc -c < "$disk" | tr -d ' ')" = 8388608 ] || { echo "disk is not 8 MiB"; exit 4; }
n=$(head -c 64 "$disk" | tr -d '\000' | wc -c | tr -d ' ')
n=$((n + 1))
head -c "$n" /dev/zero | tr '\000' x | dd of="$disk" conv=notrunc 2>/dev/null
echo "boot $n"
SH
chmod +x "$WORK/fake"/*
export PATH="$WORK/fake:$PATH"
export SOMA_MIRAGE_SWITCH=fake SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cp "$ROOT/examples/example_files/mirage_storage/mirage_storage.soma" "$WORK/run/"
cd "$WORK/run"
soma run mirage_storage.soma > "$WORK/first.log" 2> "$WORK/first-err.log"
grep -qx "boot 1" "$WORK/first.log"
grep -q "created storage.img" "$WORK/first-err.log"
test -f storage.img
soma run mirage_storage.soma > "$WORK/second.log" 2> "$WORK/second-err.log"
grep -qx "boot 2" "$WORK/second.log"
! grep -q "created" "$WORK/second-err.log"
# a program without files gets no disk
printf '%s\n' 'Require Import Sandbox.' 'Definition main : io unit := print "plain".' > plain.soma
mkdir plain && mv plain.soma plain/ && cd plain
soma run plain.soma > "$WORK/plain.log" 2> "$WORK/plain-err.log" || true
grep -qx "no storage disk given" "$WORK/plain.log"
test ! -e storage.img
echo "PASS soma run creates the storage disk once and keeps it across runs"
