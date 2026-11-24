#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$root/_build/install/default/bin/soma}
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 50 "$work"/*.log || true; fi; rm -rf "$work"' EXIT
host() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }
cat > "$work/math.definition" <<'SOMA'
From Soma Require Native.
From Corelib Require Import PrimInt63.
OCaml Native External Type real := "Float.t".
OCaml Native External Value quotient : real -> real -> PrimInt63.int :=
  "int_of_float" Composing "Stdlib.( /. )" After 0.
OCaml Native External Value earlier : real -> real -> real -> real :=
  "Stdlib.( -. )" Composing "Stdlib.( *. )" After 1.
OCaml Native External Value later : real -> real -> real -> real :=
  "Stdlib.( +. )" Composing "Stdlib.( *. )" After 1.
OCaml Native External Value ordered : PrimInt63.int -> PrimInt63.int -> PrimInt63.int -> PrimInt63.int :=
  "Fixture.outer" Composing "Fixture.inner" After 1.
SOMA
cat > "$work/main.soma" <<'SOMA'
From Soma Require Native.
Import math.
Definition main := (quotient, (earlier, (later, ordered))).
SOMA
"$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/extract.log" 2>&1
grep -q 'external-composed-value .* after 1 arity 3' "$work/native/native_abi.manifest"
cat > "$work/native/fixture.ml" <<'ML'
let phases = ref []
let inner a b = phases := "inner" :: !phases; a - b
let outer a b = phases := "outer" :: !phases; a + b
ML
cat > "$work/native/probe.ml" <<'ML'
let check label ok = if not ok then failwith label
let[@inline never] direct_quotient a b = int_of_float (a /. b)
let[@inline never] direct_relative ago now value scale =
  if ago then now -. (value *. scale) else now +. (value *. scale)
let bits = Int64.bits_of_float

let () =
  let quotient,(earlier,(later,ordered)) = Prog.soma_main () in
  let quotient = quotient () and earlier = earlier () and later = later () in
  let ordered = ordered () in
  check "native order" (ordered 20 3 11 = 12 && !(Fixture.phases) = ["outer";"inner"]);
  let values = List.map Int64.float_of_bits
      [0L; Int64.min_int; 0x3ff0000000000000L; 0xbff0000000000000L;
       0x7ff0000000000000L; 0xfff0000000000000L; 0x7ff8000000000001L;
       0xfff8000000000002L; 0x7ff0000000000003L] in
  List.iter (fun now -> List.iter (fun value -> List.iter (fun scale ->
      List.iter (fun ago ->
        let expected = bits (direct_relative ago now value scale) in
        let actual = bits ((if ago then earlier else later) now value scale) in
        if expected <> actual then failwith (Printf.sprintf
          "native relative arithmetic (ago=%b): %Lx %Lx %Lx: %Lx <> %Lx"
          ago (bits now) (bits value) (bits scale) expected actual)) [false;true];
      check "native quotient" (quotient value scale = direct_quotient value scale))
      values) values) values;
  let allocated call =
    let a = Sys.opaque_identity 180001. and b = Sys.opaque_identity 86400. in
    let start = Gc.allocated_bytes () in
    for _ = 1 to 10000 do ignore (Sys.opaque_identity (call a b)) done;
    Gc.allocated_bytes () -. start in
  check "no intermediate float allocation" (allocated quotient = allocated direct_quotient);
  print_endline "PASS: composed native expressions preserve arithmetic bits, order and allocation"
ML
configure() {
  python3 - "$work/native" <<'PY'
from pathlib import Path
import sys
root = Path(sys.argv[1])
assert 'Obj.' not in (root / 'soma_bindings.ml').read_text()
modules = sorted(path.stem for path in root.glob('*.ml') if path.stem != 'soma_main')
(root / 'dune').write_text(
    '(executable (name probe) (modes exe byte) (modules ' + ' '.join(modules)
    + ') (libraries lwt) (flags (:standard -w -a)))\n')
PY
}
configure
(cd "$work/native" && host dune build --profile release -j2 probe.exe probe.bc) > "$work/build.log" 2>&1
"$work/native/_build/default/probe.exe"
host ocamlrun "$work/native/_build/default/probe.bc"

cp "$work/math.definition" "$work/original.definition"
for position in -1 3; do
  sed "s/After 1/After $position/" "$work/original.definition" > "$work/math.definition"
  if "$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/position-$position.log" 2>&1; then
    echo "accepted invalid composition position $position" >&2
    exit 1
  fi
done
grep -q 'composition split' "$work/position-3.log"
sed 's/Stdlib.( \*. )/Stdlib.( *. ); exit 1/' "$work/original.definition" > "$work/math.definition"
if "$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/path.log" 2>&1; then
  echo "accepted invalid external operator path" >&2
  exit 1
fi
sed 's/"int_of_float" Composing/"string_of_float" Composing/' "$work/original.definition" > "$work/math.definition"
"$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/bad-extract.log" 2>&1
configure
if (cd "$work/native" && host dune build --profile release -j2) > "$work/bad-build.log" 2>&1; then
  echo "accepted a composed provider with the wrong return type" >&2
  exit 1
fi
grep -q 'soma_bindings.ml' "$work/bad-build.log"
echo 'PASS: invalid composition positions, paths and incompatible native return types rejected'
