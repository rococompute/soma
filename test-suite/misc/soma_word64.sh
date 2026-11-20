#!/usr/bin/env bash
# Soma.Word64: unsigned 64-bit words. The kernel computes the example's
# cases (its .exp proves them); an image's extraction is OCaml's int64
# (checked without an image); a C module takes and gives uint64_t, and an
# executable that calls one runs it.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 30 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
export SOMA_MIRAGE_SWITCH=nonexistent
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cd "$WORK"

# the image example: its .exp is checked (the kernel's cases are the
# expected ones), and its extraction uses Int64, unsigned
cp "$ROOT/examples/example_files/mirage_word64/"* .
soma build --no-image mirage_word64.soma > image.log 2>&1
grep -q 'mirage/plain (no image)' image.log
P="$SOMA_MIRAGE_DIR/plain"
for op in Int64.add Int64.mul Int64.unsigned_compare Soma_word64.divu Soma_word64.of_n; do
    grep -q "$op" "$P/prog.ml" || { echo "no $op in prog.ml" >&2; exit 1; }
done
[ -f "$P/soma_word64.ml" ]

# a wrong expectation is refused by the kernel
sed 's/"fffffffe00000001"/"fffffffe00000002"/' mirage_word64.soma > wrong.soma
cp mirage_word64.exp wrong.exp
if soma build --no-image wrong.soma > wrong.log 2>&1; then
    echo 'a wrong expected word was accepted' >&2; exit 1
fi
grep -q 'Unable to unify' wrong.log

# a C module with words: uint64_t both ways, through an executable
mkdir rot
cat > rot/soma.toml <<'TOML'
[project]
name = "rot"
version = "0.1.0"
TOML
cat > rot/rot.definition <<'DEF'
rotl : word64 -> int -> word64.
DEF
cat > rot/rot.c <<'C'
#include "rot.soma.h"
uint64_t rot_rotl(uint64_t w, int64_t k) {
    k &= 63;
    return k == 0 ? w : (w << k) | (w >> (64 - k));
}
C
cat > rot/main.soma <<'SOMA'
Import rot.
Require Import Soma.Word64.
main : string := Word64.to_hex (rotl (Word64.of_N 18364758544493064720%N) 8).
SOMA
# rot.c includes the generated header, so a C type other than uint64_t
# would not compile (conflicting types)
(cd rot && soma build main.soma > ../rot.log 2>&1)
[ "$(rot/main.exe)" = "dcba9876543210fe" ]
echo "word64: ok"
