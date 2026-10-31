#!/usr/bin/env bash

# A WebAssembly module, FILE.wasm, used through FILE.definition next to it
# (theories/Soma/Wasm.v, plugins/soma_wasm): its exports are checked
# against the declarations when it is compiled, computed when Soma
# evaluates, and what does not fit the declared types is a run-time error.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

# (module
#   (func (export "add") (param i64 i64) (result i64) local.get 0 local.get 1 i64.add)
#   (func (export "boom") (param i64) (result i64) unreachable)
#   (func (export "half") (param f64) (result f64) local.get 0))
printf '%s' 0061736d0100000001110360027e7e017e60017e017e60017c017c03040300010207150303616464000004626f6f6d00010468616c6600020a12030700200020017c0b0300000b040020000b \
  | xxd -r -p > m.wasm

cat > m.definition <<'EOT'
add : N -> N -> N.
boom : N -> N.
EOT
cat > prog.soma <<'EOT'
Import m.
add 2 3.
add 9223372036854775807 1.
add 9223372036854775808 0.
boom 1.
EOT
soma build -v prog.soma > out.log 2>&1
grep -q '= 5%N' out.log
# the module wraps around: an N cannot hold what it gives
grep -q 'expected an N, but got Wasm.I64 (-9223372036854775808) : Wasm.i64' out.log
# an i64 cannot hold the argument
grep -q 'expected a Wasm.i64, but got 9223372036854775808%N : N' out.log
# a trap
grep -q 'Trapped "unreachable executed"' out.log

# the kernel does not compute it: no proof goes through the module
cat > prog.proof <<'EOT'
Theorem t : add 2 3 = 5%N.
Proof.
  reflexivity.
Qed.
EOT
if soma build prog.soma > out.log 2>&1; then echo "a proof computed through the module"; exit 1; fi
rm prog.proof

# a definition is checked against the module
check() {
  printf '%s\n' "$1" > m.definition
  rm -rf .soma-cache
  if soma build prog.soma > out.log 2>&1; then echo "accepted: $1"; exit 1; fi
  grep -q "$2" out.log || { cat out.log; exit 1; }
}
printf 'Import m.\n' > prog.soma
check 'sub : N -> N -> N.' 'm.definition declares sub, which m.wasm does not export.'
check 'add : N -> N.' 'add is declared with 1 arguments'
check 'add : nat -> nat -> nat.' 'a declared type is N, Z, Any, i64 or i32'
check 'half : N -> N.' 'Soma only gives and takes i32 and i64 yet'
check 'x := 1.' 'defines nothing: x is a definition'

# soma explore lists the module's functions as escape hatches
printf 'add : N -> N -> N.\n' > m.definition
rm -rf .soma-cache
soma explore prog.soma > out.log 2>&1
grep -q "is m.wasm's add (i64, i64) -> i64, taken to be N -> N -> N" out.log
grep -q 'No issue, and no violation.' out.log
