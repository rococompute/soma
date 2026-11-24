#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$root/_build/install/default/bin/soma}
work=$(mktemp -d)
trap 'status=$?; if [ "$status" != 0 ]; then tail -n 50 "$work"/*.log || true; fi; rm -rf "$work"' EXIT
host() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }

cat >"$work/fixture.definition" <<'SOMA'
From Soma Require Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native Primitive bump : PrimInt63.int -> PrimInt63.int := "test_soma_bump" Noalloc.
OCaml Native Primitive six :
  PrimInt63.int -> PrimInt63.int -> PrimInt63.int ->
  PrimInt63.int -> PrimInt63.int -> PrimInt63.int -> PrimInt63.int :=
  "test_soma_six_byte" Native "test_soma_six_native".
OCaml Native External Callback same : forall (A : Type), A -> A := "Fun.id".
SOMA
cat >"$work/main.soma" <<'SOMA'
From Soma Require Native.
Import fixture.
Definition increment n := Native.Export (Native.Call_callback bump n).
Definition borrow text := Native.Export (Native.Call_callback (same string) text).
Definition main := (increment, six, borrow).
SOMA
"$SOMA" extract "$work/main.soma" -o "$work/native" >"$work/extract.log" 2>&1
python3 - "$work/native" <<'PY'
from pathlib import Path
import re, sys
root = Path(sys.argv[1])
def externals(name):
    return sorted(re.findall(r'^  external .+$', (root / name).read_text(), re.M))
impl, interface = map(externals, ('soma_bindings.ml', 'soma_bindings.mli'))
assert len(impl) == 2 and impl == interface, (impl, interface)
assert any('"test_soma_bump" [@@noalloc]' in row for row in impl)
assert any('"test_soma_six_byte" "test_soma_six_native"' in row for row in impl)
manifest = (root / 'native_abi.manifest').read_text()
assert manifest.count('external-primitive') == 2 and 'noalloc=true' in manifest
PY

cat >"$work/native/fixture_stubs.c" <<'C'
#include <caml/mlvalues.h>

CAMLprim value test_soma_bump(value n) { return Val_long(Long_val(n) + 1); }

static intnat digits(value a, value b, value c, value d, value e, value f)
{
  return Long_val(a) + 10 * Long_val(b) + 100 * Long_val(c) +
         1000 * Long_val(d) + 10000 * Long_val(e) + 100000 * Long_val(f);
}

CAMLprim value test_soma_six_native(value a, value b, value c, value d, value e, value f)
{
  return Val_long(digits(a, b, c, d, e, f));
}

CAMLprim value test_soma_six_byte(value *argv, int argn)
{
  if (argn != 6) return Val_long(-1);
  return Val_long(1000000 + digits(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]));
}
C
cat >"$work/native/probe.ml" <<'ML'
include Soma_bindings.Fixture
let[@inline never] direct n = bump n
let () =
  let native = Sys.backend_type = Sys.Native in
  let expected = if native then 654321 else 1654321 in
  assert (direct 29 = 30 && Prog.increment 40 = 41);
  assert (six 1 2 3 4 5 6 = expected);
  let ((_, checked_six), same) = Prog.soma_main () in
  assert (checked_six (1,(2,(3,(4,(5,6))))) = expected);
  let borrowed = Bytes.to_string (Bytes.of_string "borrowed") in
  assert (same borrowed == borrowed);
  print_endline "PASS: direct primitive interface and checked callbacks select the correct C symbol"
ML
python3 - "$work/native" <<'PY'
from pathlib import Path
import sys
root = Path(sys.argv[1])
modules = sorted(p.stem for p in root.glob('*.ml') if p.stem != 'soma_main')
(root / 'dune').write_text(
    '(executable (name probe) (modes exe byte_complete) (modules ' + ' '.join(modules) + ')'
    + ' (libraries lwt) (foreign_stubs (language c) (names fixture_stubs))'
    + ' (flags (:standard -w -a)))\n')
PY
(cd "$work/native" && host dune build --profile release -j2 probe.exe probe.bc.exe) >"$work/build.log" 2>&1
"$work/native/_build/default/probe.exe"
"$work/native/_build/default/probe.bc.exe"

negative() {
  local name=$1 declaration=$2 diagnostic=$3
  mkdir "$work/$name"
  printf 'From Soma Require Native.\n%s\n' "$declaration" >"$work/$name/bad.definition"
  printf 'Import bad.\nDefinition main := bad.\n' >"$work/$name/main.soma"
  if "$SOMA" extract "$work/$name/main.soma" -o "$work/$name/native" >"$work/$name.log" 2>&1; then
    echo "accepted invalid native primitive $name" >&2
    exit 1
  fi
  grep -q "$diagnostic" "$work/$name.log"
}
negative symbol 'OCaml Native Primitive bad : nat -> nat := "unsafe symbol".' 'C identifier'
negative native_symbol 'OCaml Native Primitive bad : nat -> nat := "valid" Native "unsafe.symbol".' 'C identifier'
negative arity 'OCaml Native Primitive bad : nat -> nat -> nat -> nat -> nat -> nat -> nat := "wide".' 'separate native symbol'
negative duplicate 'OCaml Native Primitive bad : nat -> nat -> nat -> nat -> nat -> nat -> nat := "wide" Native "wide".' 'separate native symbol'
negative label 'OCaml Native Primitive bad : forall (n : nat), nat := "labelled".' 'arguments are positional'
negative polymorphic 'OCaml Native Primitive bad : forall (A : Type), A -> A := "poly".' 'signatures must be monomorphic'
printf 'Definition main := tt.\n' >"$work/main.soma"
"$SOMA" extract "$work/main.soma" -o "$work/native" >"$work/obsolete.log" 2>&1
test ! -e "$work/native/soma_bindings.mli"
echo 'PASS: malformed primitive declarations rejected and obsolete generated interface reclaimed'
