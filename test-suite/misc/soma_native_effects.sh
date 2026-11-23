#!/usr/bin/env bash
# Extract once, build the generated project, call its actual entry points from
# native and bytecode clients. No project-specific runtime or interpreter.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 70 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
cp "$ROOT/examples/example_files/native_effects/native_effects.soma" "$WORK/main.soma"
cd "$WORK"
soma extract main.soma -o native > extract.log 2>&1
soma hash main.soma > hash.log 2>&1
if grep -q '  assumes ' hash.log; then
 echo 'native library example introduced logical assumptions' >&2; exit 1
fi
test -f native/soma_effect.ml
test -f native/soma_handles.ml
test ! -f native/config.ml
grep -q '(libraries lwt)' native/dune
(cd native && dune build --profile release) > build.log 2>&1
cp native/{prog.ml,prog.mli,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml} .
cp "$ROOT/test-suite/misc/soma_native_effects_runtime.ml" check.ml
for compiler in ocamlc ocamlopt; do
  ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
    soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml > "$compiler.log" 2>&1
  "./check-$compiler"
done
# Foreign callers can accept native entry callbacks at their real native type.
mkdir foreign
printf '[project]\nname = "native_entry_signature"\nversion = "0.1.0"\n' > foreign/soma.toml
cat > foreign/caller.definition <<'SOMA'
Require Import Soma.Native.
check : (unit -> entry nat) -> nat.
SOMA
printf 'let check f = f ()\n' > foreign/caller.ml
cat > foreign/main.soma <<'SOMA'
Require Import Soma.Native.
Import caller.
Definition main : entry nat := Export (Invoke
 (fun _ => check (fun _ => Export (Return 42))) Return).
SOMA
(cd foreign && soma extract main.soma -o native && cd native && dune build --profile release) > signature.log 2>&1
printf 'let check (_ : unit -> string) = 0\n' > foreign/caller.ml
(cd foreign && soma extract main.soma -o native) > bad-signature.log 2>&1
if (cd foreign/native && dune build --profile release) >> bad-signature.log 2>&1; then
 echo 'accepted a foreign callback with the wrong native entry type' >&2; exit 1
fi
grep -q 'Soma_effect.entry\|int\|Soma_nat.nat' bad-signature.log
# A native result cannot be converted back into its original effect program.
cat > inspect.soma <<'SOMA'
Require Import Soma.Native.
Definition inspect (value : entry nat) : program nat :=
 match value with Export body => body end.
Definition main := inspect.
SOMA
if soma extract inspect.soma -o inspected > inspect-extract.log 2>&1; then
  echo 'accepted inspection of a native entry' >&2; exit 1
fi
grep -q 'Native programs and entry points cannot be inspected' inspect-extract.log
# The same generated library boundaries work inside an image, with a native
# caller standing in for Kykeon's current entry-point consumers.
mkdir image
printf '[project]\nname = "native_entry_image"\nversion = "0.1.0"\n' > image/soma.toml
cat > image/caller.definition <<'SOMA'
Require Import Soma.Native.
invoke : (unit -> entry (promise nat)) -> promise nat.
SOMA
printf 'let invoke f = f ()\n' > image/caller.ml
cat > image/main.soma <<'SOMA'
Require Import Sandbox.
Require Import Soma.Native.
Import caller.
Definition main : io unit :=
 pending <- call (fun _ => invoke (fun _ => Native.Export (Native.Promise_return 42))) ;;
 value <- await_promise pending ;;
 if Nat.eqb value 42 then print "native library boundary in Solo5 verified" else exit 1.
SOMA
(cd image && SOMA_MIRAGE_DIR="$WORK/image-project" soma build --no-image main.soma) > image-check.log 2>&1
if [ "${SOMA_TEST_HVF:-0}" = 1 ]; then
 (cd image && SOMA_MIRAGE_DIR="$WORK/image-project" soma build main.soma) > image-build.log 2>&1
 timeout 20 opam exec --switch="${SOMA_MIRAGE_SWITCH:-hvf}" -- solo5-hvt --mem=256 -- image/main.hvt > image-boot.log 2>&1
 grep -q 'native library boundary in Solo5 verified' image-boot.log
fi
echo 'native library effects: ok'
