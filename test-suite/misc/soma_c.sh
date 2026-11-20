#!/usr/bin/env bash
# C modules: FILE.c next to FILE.definition. An executable that calls one
# runs it; a C function that does not match its declaration, or a
# declaration C cannot take, is refused; more than five arguments go
# through OCaml's bytecode convention too; an image's C is checked
# without an image, and call puts C calls in order.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 30 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
export SOMA_MIRAGE_SWITCH=nonexistent
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE

# an executable: ints, floats, strings, an option, a handle
cp -R "$ROOT/examples/example_projects/c_arith" "$WORK/arith"
rm -rf "$WORK/arith/.soma-cache" "$WORK/arith/main.exe"
(cd "$WORK/arith" && soma build main.soma > "$WORK/arith.log" 2>&1)
[ "$("$WORK/arith/main.exe")" = "42 HELLO! 65 none 1" ]

# six arguments, and a C function whose type is not its declaration's
mkdir "$WORK/six"
cat > "$WORK/six/soma.toml" <<'TOML'
[project]
name = "six"
version = "0.1.0"
TOML
cat > "$WORK/six/many.definition" <<'DEF'
weigh : int -> int -> int -> int -> int -> int -> int.
DEF
cat > "$WORK/six/many.c" <<'C'
#include "many.soma.h"
int64_t many_weigh(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f) {
    return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f;
}
C
cat > "$WORK/six/main.soma" <<'SOMA'
Import many.
main : string := to_string (weigh 1 1 1 1 1 1).
SOMA
(cd "$WORK/six" && soma build main.soma > "$WORK/six.log" 2>&1)
[ "$("$WORK/six/main.exe")" = "21" ]
sed -i.bak 's/int64_t a, int64_t b/double a, int64_t b/' "$WORK/six/many.c"
if (cd "$WORK/six" && soma build main.soma > "$WORK/mismatch.log" 2>&1); then
    echo 'a C function unlike its declaration was built' >&2; exit 1
fi
grep -q 'conflicting types' "$WORK/mismatch.log"

# a declaration C cannot take
mkdir "$WORK/list"
cp "$WORK/six/soma.toml" "$WORK/list/"
printf 'total : list nat -> nat.\n' > "$WORK/list/sums.definition"
printf '#include "sums.soma.h"\n' > "$WORK/list/sums.c"
printf 'Import sums.\nmain : string := to_string (total [1, 2]).\n' > "$WORK/list/main.soma"
if (cd "$WORK/list" && soma build main.soma > "$WORK/list.log" 2>&1); then
    echo 'a list given to C passed' >&2; exit 1
fi
grep -q 'is not given to C' "$WORK/list.log"

# an image's C: its OCaml and C checked without an image, in a library
# of its own; call is extracted
cp -R "$ROOT/examples/example_projects/c_image" "$WORK/image"
rm -rf "$WORK/image/.soma-cache"
(cd "$WORK/image" && soma build --no-image main.soma > "$WORK/image.log" 2>&1)
grep -q 'plain-c-ocaml-.* (no image)' "$WORK/image.log"
P=$(ls -d "$SOMA_MIRAGE_DIR"/plain-c-ocaml-*)
grep -q '"soma_c"' "$P/config.ml"
grep -q 'foreign_stubs (language c) (names machine_soma_stubs machine_soma_c)' "$P/soma_c/dune"
grep -q 'Call' "$P/prog.ml"
[ ! -e "$P/machine.ml" ]
sed -i.bak 's/int64_t machine_buffer_sum(soma_handle h)/double machine_buffer_sum(soma_handle h)/' "$WORK/image/machine.c"
if (cd "$WORK/image" && soma build --no-image main.soma > "$WORK/image-mismatch.log" 2>&1); then
    echo 'an image C function unlike its declaration passed the check' >&2; exit 1
fi
grep -q 'conflicting types' "$WORK/image-mismatch.log"
