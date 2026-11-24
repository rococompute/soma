#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$root/_build/install/default/bin/soma}
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 60 "$work"/*.log || true; fi; rm -rf "$work"' EXIT
host() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }

cat > "$work/forms.definition" <<'SOMA'
From Soma Require Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Type form := "Host.form".
OCaml Native Constructor empty : unit -> form := "Host.Empty" 0.
OCaml Native Constructor reference : reference string -> form := "Ref" 1.
OCaml Native Constructor single_tuple : (PrimInt63.int * string)%type -> form := "Single_tuple" 1.
OCaml Native Constructor multi_field : PrimInt63.int -> string -> form := "Host.Multi_field" 2.
OCaml Native Constructor make_failure : string -> exception_value := "Stdlib.Failure" 1.
SOMA
cat > "$work/main.soma" <<'SOMA'
From Soma Require Native.
Import forms.
Definition make_empty (_ : unit) := Native.Export (Native.Call_callback empty tt).
Definition make_reference value := Native.Export (Native.Call_callback reference value).
Definition make_tuple value := Native.Export (Native.Call_callback single_tuple value).
Definition make_fields count text := Native.Export (Native.Call_callback multi_field (count,text)).
Definition fail text := Native.Export (
  Native.Bind (Native.Call_callback make_failure text) (fun error => Native.Throw error)).
Definition main := (make_empty, make_reference, make_tuple, make_fields, fail).
SOMA
cat > "$work/host.ml" <<'ML'
type form =
  | Empty
  | Ref of string ref
  | Single_tuple of (int * string)
  | Multi_field of int * string
ML
cat > "$work/probe.ml" <<'ML'
let check message condition = if not condition then failwith message
let () =
  let payload = Bytes.to_string (Bytes.make 256 's') in
  let location = ref payload and pair = (19, payload) in
  check "nullary constructor identity" (Prog.make_empty () == Host.Empty);
  check "unary reference identity"
    (match Prog.make_reference location with Host.Ref actual -> actual == location | _ -> false);
  check "single pair payload identity"
    (match Prog.make_tuple pair with Host.Single_tuple actual -> actual == pair | _ -> false);
  check "two constructor fields"
    (match Prog.make_fields 19 payload with Host.Multi_field (19, actual) -> actual == payload | _ -> false);
  check "exception payload identity"
    (try Prog.fail payload; false with Failure actual -> actual == payload | _ -> false);
  print_endline "PASS: typed ordinary nullary, reference, single-tuple and multi-field constructors and exception payload identity"
ML

compile_probe() {
  local directory=$1
  cp "$work/host.ml" "$work/probe.ml" "$directory/"
  python3 - "$directory" <<'PY'
from pathlib import Path
import sys

directory = Path(sys.argv[1])
assert 'Obj.' not in (directory / 'soma_bindings.ml').read_text()
modules = sorted(p.stem for p in directory.glob('*.ml') if p.stem != 'soma_main')
(directory / 'dune').write_text(
    '(executable (name probe) (modes exe byte) (modules ' + ' '.join(modules)
    + ') (libraries lwt) (flags (:standard -w -a)))\n'
)
PY
  (cd "$directory" && host dune build --profile release -j2 probe.exe probe.bc)
}

"$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/extract.log" 2>&1
grep -q 'constructor-build' "$work/native/native_abi.manifest"

compile_probe "$work/native" > "$work/build.log" 2>&1
"$work/native/_build/default/probe.exe"
host ocamlrun "$work/native/_build/default/probe.bc"

mv "$work/forms.definition" "$work/forms.original"
sed 's/empty : unit/empty : bool/' "$work/forms.original" > "$work/forms.definition"
if "$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/unit.log" 2>&1; then
  echo "accepted a non-unit nullary constructor argument" >&2
  exit 1
fi
grep -q 'a nullary Constructor takes unit' "$work/unit.log"

sed 's/"Host.Multi_field" 2/"Host.Multi_field" 1/' "$work/forms.original" > "$work/forms.definition"
if "$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/arity.log" 2>&1; then
  echo "accepted a constructor returning a residual function" >&2
  exit 1
fi
grep -q 'constructor operations need a declared native type' "$work/arity.log"


sed 's/multi_field : PrimInt63.int -> string/multi_field : string -> string/' \
  "$work/forms.original" > "$work/forms.definition"
sed -i 's/(count,text)/(text,count)/' "$work/main.soma"
"$SOMA" extract "$work/main.soma" -o "$work/bad-native" > "$work/bad-extract.log" 2>&1
if compile_probe "$work/bad-native" > "$work/bad-build.log" 2>&1; then
  echo "accepted a string for an integer constructor field" >&2
  exit 1
fi
grep -q 'soma_bindings.ml' "$work/bad-build.log"
grep -q 'int' "$work/bad-build.log"
echo 'PASS: invalid nullary input and incompatible ordinary constructor fields rejected'
