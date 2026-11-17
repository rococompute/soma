#!/usr/bin/env bash
# Native OCaml declarations in a Sandbox program: type-check the generated
# image without Mirage/Solo5. dev/ocaml-mirage-check.sh boots the real target.
set -euo pipefail
export PATH="$BIN:$PATH"
HERE=$(cd "$(dirname "$0")/../.." && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
export SOMA_MIRAGE_DIR="$TMP/mirage"
export SOMA_MIRAGE_SWITCH=
unset SOMA_OCAML_BUILD
cd "$TMP"
mkdir app
cd app
cat > tools.ml <<'EOF'
type 'a box = Box of 'a
let wrap x = Box x
let unbox (Box x) = x
let twice f x = f (f x)
let next (n : Soma_nat.nat) : Soma_nat.nat = n + 1
let named ~prefix s = prefix ^ s
let half x = x /. 2.
EOF
cat > tools.definition <<'EOF'
box : Type -> Type.
wrap : forall {A}, A -> box A.
unbox : forall {A}, box A -> A.
twice : forall {A}, (A -> A) -> A -> A.
next : nat -> nat.
named : forall (prefix : string), string -> string.
half : float -> float.
EOF
cat > string.definition <<'EOF'
uppercase_ascii : string -> string.
EOF
cat > main.soma <<'EOF'
Import Sandbox tools string.
main : io unit :=
  print (uppercase_ascii (named "native " (unbox (wrap "OCaml")))) ;;
  print (to_string (twice next 40)) ;;
  print (if PrimFloat.eqb (half 4.0) 2.0 then "float ok" else "float bad").
EOF
soma build --no-image main.soma > out.log 2>&1 || { cat out.log; exit 1; }
dir=$(find "$SOMA_MIRAGE_DIR" -name soma_bindings.ml -not -path '*/no-image/*' -exec dirname {} \;)
test -n "$dir"
grep -q 'Tools.named ~prefix:a0 a1' "$dir/soma_bindings.ml"
grep -q 'Soma_bindings.tools__next' "$dir/prog.ml"
test -f "$dir/soma_nat.ml"
test -f "$dir/no-image/tools.cmi"
! test -f main.exe

# A wrong declaration must fail in OCaml, with the original module path.
sed -i.bak 's/let next .*$/let next n = "not a nat"/' tools.ml
if soma build --no-image main.soma > out.log 2>&1; then
  echo 'a false OCaml declaration was accepted in an image'; exit 1
fi
grep -q 'Soma_bindings\|soma_bindings' out.log
grep -q 'string' out.log

# Replacing a module in the same program removes the old generated source.
printf 'let message = "replacement"\n' > other.ml
printf 'message : string.\n' > other.definition
printf 'Import Sandbox other.\nmain : io unit := print message.\n' > main.soma
soma build --no-image main.soma > out.log 2>&1 || { cat out.log; exit 1; }
test -f "$dir/other.ml"
! test -f "$dir/tools.ml"

# Do not overwrite the image's own runtime modules.
printf 'let message = "bad"\n' > soma_rt.ml
printf 'message : string.\n' > soma_rt.definition
printf 'Import Sandbox soma_rt.\nmain : io unit := print message.\n' > main.soma
if soma build --no-image main.soma > out.log 2>&1; then
  echo 'an application overwrote the image runtime'; exit 1
fi
grep -q 'the name of one Soma makes' out.log

# A local module can use declared findlib libraries; native sublibrary
# names and exact package versions must reach the Mirage configuration.
cat > replacer.ml <<'EOF'
let replace s = Str.global_replace (Str.regexp "old") "new" s
EOF
printf 'OCaml Library "str".\nreplace : string -> string.\n' > replacer.definition
printf 'Import Sandbox replacer.\nmain : io unit := print (replace "old").\n' > main.soma
soma build --no-image main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q '~local_libs:\["str"\]' "$dir/config.ml"

# Native bindings and WASM bindings must coexist in the same extraction.
cp "$HERE/examples/example_projects/wasm_add/add.wasm" add.wasm
printf 'add : N -> N -> N.\n' > add.definition
printf 'message : string.\n' > other.definition
cat > main.soma <<'EOF'
Import Sandbox other add.
main : io unit := print message ;; print (to_string (add 1 2)).
EOF
soma build --no-image main.soma > out.log 2>&1 || { cat out.log; exit 1; }
mixed=$(find "$SOMA_MIRAGE_DIR" -name prog.ml -path '*/plain-wasm-ocaml-*/*' -not -path '*/no-image/*')
grep -q 'Soma_wasm.call' "$mixed"
grep -q 'Soma_bindings.other__message' "$mixed"

# Host-only declarations still fail before trying to configure Mirage.
printf 'OCaml Library "unix".\nmessage : string.\n' > other.definition
printf 'Import Sandbox other.\nmain : io unit := print message.\n' > main.soma
if soma build --no-image main.soma > out.log 2>&1; then
  echo 'a host-only library was accepted'; exit 1
fi
grep -q 'requires the host runtime' out.log
