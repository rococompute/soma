#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$root/_build/install/default/bin/soma}
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 60 "$work"/*.log || true; fi; rm -rf "$work"' EXIT
host() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }

cat > "$work/family.definition" <<'SOMA'
From Soma Require Native.
From Stdlib Require Import Strings.String.
OCaml Native External Type variant (A : Type) := "Host.variant".
OCaml Native External Type handle (A : Type; B : Type) := "Host.handle".
OCaml Native Constructor make : forall A : Type, A -> variant A := "Host.Value" 1.
OCaml Native Case take : forall A : Type, variant A -> option A := "Host.Value" 1.
OCaml Native Build pack : forall (A B : Type), variant A -> B -> handle A B := "variant" "marker".
OCaml Native Get marker : forall (A B : Type), handle A B -> B := "marker".
SOMA
cat > "$work/main.soma" <<'SOMA'
From Soma Require Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
Import family.
Definition boxed value := Native.Export (Native.Call_callback (make string) value).
Definition unbox value := Native.Export (Native.Call_callback (take string) value).
Definition packed value key := Native.Export (Native.Call_callback (pack string PrimInt63.int) (value, key)).
Definition get_marker value := Native.Export (Native.Call_callback (marker string PrimInt63.int) value).
Definition make_polymorphic {A : Type} value := Native.Export (Native.Call_callback (make A) value).
Definition main := (boxed, unbox, packed, get_marker, @make_polymorphic).
SOMA

"$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/extract.log" 2>&1
grep -q 'native-external-family' "$work/native/native_abi.manifest"
cat > "$work/native/host.ml" <<'ML'
type 'a variant = Empty | Value of 'a
type ('a, 'b) handle = { variant : 'a variant; marker : 'b }
ML
cat > "$work/native/probe.ml" <<'ML'
let check name condition = if not condition then failwith name
let () =
  let payload = Bytes.to_string (Bytes.make 256 't') in
  let value = Prog.boxed payload in
  check "raw constructor payload" (match value with Host.Value s -> s == payload | _ -> false);
  check "raw destructor payload" (match Prog.unbox value with Some s -> s == payload | _ -> false);
  check "nullary alternate" (Prog.unbox Host.Empty = None);
  let packed = Prog.packed value 211 in
  check "native pair family" (packed.Host.variant == value && Prog.get_marker packed = 211);
  check "generic export" (match Prog.make_polymorphic (ref payload) with Host.Value r -> !r == payload | _ -> false);
  print_endline "PASS: typed native external families preserve record/variant types and pointer identities"
ML
python3 - "$work/native" <<'PY'
from pathlib import Path
import sys
directory = Path(sys.argv[1])
assert 'Obj.' not in (directory / 'soma_bindings.ml').read_text()
modules = sorted(p.stem for p in directory.glob('*.ml') if p.stem != 'soma_main')
(directory / 'dune').write_text(
    '(executable (name probe) (modes exe byte) (modules ' + ' '.join(modules)
    + ') (libraries lwt) (flags (:standard -w -a)))\n')
PY
(cd "$work/native" && host dune build --profile release -j2 probe.exe probe.bc) > "$work/build.log" 2>&1
"$work/native/_build/default/probe.exe"
host ocamlrun "$work/native/_build/default/probe.bc"

cp "$work/main.soma" "$work/good.soma"
cat > "$work/main.soma" <<'SOMA'
From Soma Require Native.
From Stdlib Require Import Strings.String.
Import family.
Definition interchange (value : variant string) : variant bool := value.
Definition main := interchange.
SOMA
if "$SOMA" extract "$work/main.soma" -o "$work/invalid" > "$work/interchange.log" 2>&1; then
  echo "accepted interchangeable instantiations of a native external family" >&2
  exit 1
fi
grep -q 'while it is expected to have type' "$work/interchange.log"
mv "$work/good.soma" "$work/main.soma"
cat >> "$work/family.definition" <<'SOMA'
OCaml Native External Type invalid (N : string) := "Host.variant".
SOMA
if "$SOMA" extract "$work/main.soma" -o "$work/invalid" > "$work/sort.log" 2>&1; then
  echo "accepted a value as a native external type parameter" >&2
  exit 1
fi
grep -q 'native type parameters must have sort Type or Set' "$work/sort.log"
