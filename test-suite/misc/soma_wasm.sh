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
grep -q 'expected an N, but got I64 (-9223372036854775808) : i64' out.log
# an i64 cannot hold the argument
grep -q 'expected an i64, but got 9223372036854775808%N : N' out.log
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
check 'add : nat -> nat -> nat.' 'a declared type is N, Z, float, Any, i64 or i32'
check 'half : N -> N.' "half: N is not m.wasm's f64."
check 'x := 1.' 'defines nothing: x is a definition'

# floats: half takes and gives an f64, declared as a float
printf 'half : float -> float.\n' > m.definition
rm -rf .soma-cache
printf 'Import m.\nhalf 2.5.\n(boom 1 : Z).\n' > prog.soma
soma build -v prog.soma > out.log 2>&1
grep -q '= 2.5%float' out.log
# boom, which it does not declare, is of type Any
grep -q 'Trapped "unreachable executed"' out.log

# an image calls a module's declared functions; one of type Any, it cannot
# yet, and says so (refused before the image is built)
printf 'Import Sandbox.\nImport m.\nmain : io unit := print (to_string ((boom 1 : Z))).\n' > img.soma
if soma build img.soma > out.log 2>&1; then echo "an image called an export of type Any"; exit 1; fi
grep -q "main calls m.boom, m.wasm's boom, of type Any," out.log
grep -q 'declare its type in m.definition' out.log
rm img.soma

# a module without a definition: its exports are of type Any; what it gives
# is a Z, which a cast checks; an Any that holds no number is an error
rm m.definition
rm -rf .soma-cache
cat > prog.soma <<'EOT'
Import m.
Check add.
(add 2 3 : Z).
(add 2 3 : N).
add "two" 3.
EOT
soma build -v prog.soma > out.log 2>&1
grep -q 'Any -> Any -> Any' out.log
grep -q '= 5%Z' out.log
grep -q 'expected an N, but got 5%Z : Z' out.log
grep -q 'expected an i64, but got "two" : string' out.log
# a float in an Any is a float; a nat is no float
printf 'Import m.\n(half 2.5%%float : float).\n(half 2 : float).\n' > prog.soma
soma build -v prog.soma > out.log 2>&1
grep -q '= 2.5%float' out.log
grep -q 'expected a float, but got 2 : nat' out.log
# an export a definition does not declare is of type Any too
printf 'add : N -> N -> N.\n' > m.definition
rm -rf .soma-cache
printf 'Import m.\nCheck boom.\n' > prog.soma
soma build -v prog.soma > out.log 2>&1
grep -q 'Any -> Any' out.log
printf 'Import m.\n' > prog.soma

# soma explore lists the module's functions as escape hatches
printf 'add : N -> N -> N.\n' > m.definition
rm -rf .soma-cache
soma explore prog.soma > out.log 2>&1
grep -q "is m.wasm's add (i64, i64) -> i64, taken to be N -> N -> N" out.log
grep -q 'No issue, and no violation.' out.log
