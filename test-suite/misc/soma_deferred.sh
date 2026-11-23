#!/usr/bin/env bash
# Generated interfaces and actual deferred runtime branches, using real Lwt.
# Set SOMA_TEST_HVF=1 for the complete Source program in a Solo5 guest.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 50 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cp "$ROOT/examples/example_files/mirage_deferred/mirage_deferred.soma" "$WORK/main.soma"
cd "$WORK"
soma build --no-image main.soma > build.log 2>&1
P="$SOMA_MIRAGE_DIR/plain"
grep -q 'Soma_handles.deferred' "$P/prog.mli"
grep -q "^type 'a deferred$" "$P/no-image/soma_handles.ml"
grep -q "^type 'a deferred = 'a Lwt.t Lazy.t$" "$P/soma_handles.ml"

# A native signature can name the handle; its value type is checked.
mkdir foreign
cat > foreign/soma.toml <<'TOML'
[project]
name = "deferred_signature"
version = "0.1.0"
TOML
printf 'identity : deferred nat -> deferred nat.\n' > foreign/bridge.definition
printf 'let identity (d : int Soma_handles.deferred) = d\n' > foreign/bridge.ml
cat > foreign/main.soma <<'SOMA'
Require Import Sandbox.
Import bridge.
main : io unit :=
  d <- new_deferred (fun _ => ret 42) ;;
  d <- call (fun _ => identity d) ;;
  n <- force_deferred d ;; if Nat.eqb n 42 then ret tt else exit 1.
SOMA
(cd foreign && SOMA_MIRAGE_DIR="$WORK/foreign-image" soma build --no-image main.soma > ../signature.log 2>&1)
printf 'let identity (_ : int Soma_handles.deferred) : bool Soma_handles.deferred = failwith "unused"\n' > foreign/bridge.ml
if (cd foreign && SOMA_MIRAGE_DIR="$WORK/bad-image" soma build --no-image main.soma > ../bad-signature.log 2>&1); then
    echo 'accepted a deferred handle with the wrong result type' >&2; exit 1
fi
grep -q 'bool.*Soma_handles.deferred' bad-signature.log

if command -v ocamlfind >/dev/null && ocamlfind query lwt >/dev/null 2>&1; then
    OCAMLC=(ocamlfind ocamlc -package lwt -linkpkg)
else
    echo 'deferred: interface checks passed; real runtime tests require ocamlfind lwt' >&2
    exit 1
fi
cp "$P"/{prog.ml,prog.mli,uint63.ml,soma_word64.ml,soma_handles.ml,float64.ml} .
# Extract the actual emitted cases, not a second implementation of deferred
# semantics. The tiny harness only needs these three effects.
python3 - "$P/soma_rt.ml" > runtime.ml <<'PY'
import sys
text = open(sys.argv[1]).read()
start = text.index('  | Prog.New_deferred body ->')
end = text.index('  | Prog.Yield ->', start)
await_start = text.index('  | Prog.Await_promise p ->')
print('let check = Prog.Gradual_rt.check')
print("let rec run : 'a. unit -> 'a Prog.io -> 'a Lwt.t = fun net m -> match check m with")
print(text[await_start:end])
print('  | _ -> failwith "unexpected effect in deferred runtime test"')
PY
cp "$ROOT/test-suite/misc/soma_deferred_runtime.ml" check.ml
"${OCAMLC[@]}" -w -a -c uint63.ml soma_word64.ml soma_handles.ml float64.ml prog.mli prog.ml runtime.ml check.ml > compile.log 2>&1
"${OCAMLC[@]}" -o check uint63.cmo soma_word64.cmo soma_handles.cmo float64.cmo prog.cmo runtime.cmo check.cmo >> compile.log 2>&1
./check
if [ "${SOMA_TEST_HVF:-0}" = 1 ]; then
    soma build main.soma > image.log 2>&1
    timeout 20 opam exec --switch="${SOMA_MIRAGE_SWITCH:-hvf}" -- solo5-hvt --mem=256 -- main.hvt > boot.log 2>&1
    grep -q 'deferred computation sharing, failure, reentry and cancellation verified' boot.log
fi
echo 'deferred: ok'
