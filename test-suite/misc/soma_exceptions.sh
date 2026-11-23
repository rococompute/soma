#!/usr/bin/env bash
# Original native exceptions through the generated backend and typed signatures.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 60 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cp "$ROOT/examples/example_files/mirage_exceptions/mirage_exceptions.soma" "$WORK/main.soma"
cd "$WORK"
soma build --no-image main.soma > build.log 2>&1
P="$SOMA_MIRAGE_DIR/plain"
grep -q 'Soma_handles.exception_value' "$P/prog.mli"
grep -q '^type exception_value = exn$' "$P/soma_handles.ml"
mkdir foreign
cat > foreign/soma.toml <<'TOML'
[project]
name = "exception_signature"
version = "0.1.0"
TOML
cat > foreign/native.definition <<'SOMA'
OCaml Library "lwt".
marker : unit -> exception_value.
classify : exception_value -> option nat.
explode : unit -> nat.
reject : unit -> promise nat.
SOMA
cat > foreign/native.ml <<'OCAML'
exception Returned of int
let error = Returned 42
let marker () = error
let classify = function Returned n -> Some n | _ -> None
let explode () = raise error
let reject () = Lwt.fail error
OCAML
cat > foreign/main.soma <<'SOMA'
Require Import Sandbox.
Import native.
check (ok : bool) : io unit := if ok then ret tt else exit 1.
main : io unit :=
  expected <- call marker ;;
  sync <- catch (call explode ;; ret expected) (fun error => ret error) ;;
  later <- call reject ;;
  async <- catch (await_promise later ;; ret expected) (fun error => ret error) ;;
  a <- same_exception expected sync ;; b <- same_exception expected async ;;
  tag <- call (fun _ => classify async) ;;
  check (a && b && match tag with Some 42 => true | _ => false end) ;;
  print "native exception signatures and identity verified".
SOMA
(cd foreign && SOMA_MIRAGE_DIR="$WORK/foreign-image" soma build --no-image main.soma > ../signature.log 2>&1)
cp foreign/native.ml foreign/native.good
printf 'let marker () = "wrong"\nlet classify (_ : string) = None\nlet explode () = 0\nlet reject () = Lwt.return 0\n' > foreign/native.ml
if (cd foreign && SOMA_MIRAGE_DIR="$WORK/bad-image" soma build --no-image main.soma > ../bad-signature.log 2>&1); then
    echo 'accepted a string as a native exception' >&2; exit 1
fi
grep -q 'exception_value\|exn' bad-signature.log
mv foreign/native.good foreign/native.ml
if command -v ocamlfind >/dev/null && ocamlfind query lwt >/dev/null 2>&1; then
    OCAMLC=(ocamlfind ocamlc -package lwt -linkpkg)
else
    echo 'exceptions: runtime tests require ocamlfind lwt' >&2; exit 1
fi
cp "$P"/{prog.ml,prog.mli,uint63.ml,soma_word64.ml,soma_handles.ml,float64.ml} .
python3 - "$P/soma_rt.ml" > runtime.ml <<'PY'
import re, sys
text = open(sys.argv[1]).read()
print('open Lwt.Infix\nexception Exit_with of int\nlet check = Prog.Gradual_rt.check')
print('let string_of_chars s = s\nlet chars_of_string s = s')
print("let rec run : 'a. unit -> 'a Prog.io -> 'a Lwt.t = fun net m -> match check m with")
for name in ('Ret', 'Bind', 'Call', 'Await_promise', 'Catch', 'Throw_exception',
             'New_failure', 'Exception_message', 'Same_exception', 'Finally'):
    start = text.index('  | Prog.' + name + ' ')
    end = start + 1 + re.search(r'^  \| Prog\.', text[start+1:], re.M).start()
    print(text[start:end])
print('  | _ -> failwith "unexpected effect in exception runtime test"')
PY
cp "$ROOT/test-suite/misc/soma_exceptions_runtime.ml" check.ml
"${OCAMLC[@]}" -w -a -c uint63.ml soma_word64.ml soma_handles.ml float64.ml prog.mli prog.ml runtime.ml check.ml > compile.log 2>&1
"${OCAMLC[@]}" -o check uint63.cmo soma_word64.cmo soma_handles.cmo float64.cmo prog.cmo runtime.cmo check.cmo >> compile.log 2>&1
./check
if [ "${SOMA_TEST_HVF:-0}" = 1 ]; then
    soma build main.soma > image.log 2>&1
    timeout 20 opam exec --switch="${SOMA_MIRAGE_SWITCH:-hvf}" -- solo5-hvt --mem=256 -- main.hvt > boot.log 2>&1
    grep -q 'exception identity, rethrow, scoped cleanup and cancellation verified' boot.log
    (cd foreign && SOMA_MIRAGE_DIR="$WORK/foreign-image" soma build main.soma > ../foreign-image.log 2>&1)
    timeout 20 opam exec --switch="${SOMA_MIRAGE_SWITCH:-hvf}" -- solo5-hvt --mem=256 -- foreign/main.hvt > foreign-boot.log 2>&1
    grep -q 'native exception signatures and identity verified' foreign-boot.log
    cat > exit.soma <<'SOMA'
Require Import Sandbox.
main : io unit := catch (exit 7) (fun _ => print "exit swallowed" ;; exit 1).
SOMA
    soma build exit.soma > exit-image.log 2>&1
    set +e
    timeout 20 opam exec --switch="${SOMA_MIRAGE_SWITCH:-hvf}" -- solo5-hvt --mem=256 -- exit.hvt > exit-boot.log 2>&1
    rc=$?
    set -e
    [ "$rc" = 7 ]
    ! grep -q 'exit swallowed' exit-boot.log
fi
echo 'exceptions: ok'
