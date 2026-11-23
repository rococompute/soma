#!/usr/bin/env bash
# Reference effects, native signatures and generated runtime with real Lwt.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 50 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cp "$ROOT/examples/example_files/mirage_references/mirage_references.soma" "$WORK/main.soma"
cd "$WORK"
soma build --no-image main.soma > build.log 2>&1
P="$SOMA_MIRAGE_DIR/plain"
grep -q 'Soma_handles.reference' "$P/prog.mli"
grep -q "^type 'a reference = 'a ref$" "$P/soma_handles.ml"

mkdir foreign
cat > foreign/soma.toml <<'TOML'
[project]
name = "reference_signature"
version = "0.1.0"
TOML
printf 'bump : reference nat -> unit.\n' > foreign/bridge.definition
printf 'let bump (r : int ref) = incr r\n' > foreign/bridge.ml
cat > foreign/main.soma <<'SOMA'
Require Import Sandbox.
Import bridge.
main : io unit :=
  r <- new_reference 41 ;; call (fun _ => bump r) ;;
  n <- read_reference r ;; if Nat.eqb n 42 then ret tt else exit 1.
SOMA
(cd foreign && SOMA_MIRAGE_DIR="$WORK/foreign-image" soma build --no-image main.soma > ../signature.log 2>&1)
printf 'let bump (r : bool ref) = r := true\n' > foreign/bridge.ml
if (cd foreign && SOMA_MIRAGE_DIR="$WORK/bad-image" soma build --no-image main.soma > ../bad-signature.log 2>&1); then
    echo 'accepted a reference with the wrong value type' >&2; exit 1
fi
grep -q 'bool ref' bad-signature.log

if command -v ocamlfind >/dev/null && ocamlfind query lwt >/dev/null 2>&1; then
    OCAMLC=(ocamlfind ocamlc -package lwt -linkpkg)
else
    echo 'references: interface checks passed; runtime tests require ocamlfind lwt' >&2
    exit 1
fi
cp "$P"/{prog.ml,prog.mli,uint63.ml,soma_word64.ml,soma_handles.ml,float64.ml} .
python3 - "$P/soma_rt.ml" > runtime.ml <<'PY'
import sys
text = open(sys.argv[1]).read()
start = text.index('  | Prog.New_reference value ->')
end = text.index('  | Prog.Yield ->', start)
print('let check = Prog.Gradual_rt.check')
print("let run : 'a. unit -> 'a Prog.io -> 'a Lwt.t = fun _ m -> match check m with")
print(text[start:end])
print('  | _ -> failwith "unexpected effect in reference runtime test"')
PY
cp "$ROOT/test-suite/misc/soma_references_runtime.ml" check.ml
"${OCAMLC[@]}" -w -a -c uint63.ml soma_word64.ml soma_handles.ml float64.ml prog.mli prog.ml runtime.ml check.ml > compile.log 2>&1
"${OCAMLC[@]}" -o check uint63.cmo soma_word64.cmo soma_handles.cmo float64.cmo prog.cmo runtime.cmo check.cmo >> compile.log 2>&1
./check
if [ "${SOMA_TEST_HVF:-0}" = 1 ]; then
    soma build main.soma > image.log 2>&1
    timeout 20 opam exec --switch="${SOMA_MIRAGE_SWITCH:-hvf}" -- solo5-hvt --mem=256 -- main.hvt > boot.log 2>&1
    grep -q 'reference aliases, updates, failure, deferred reads and cycles verified' boot.log
fi
echo 'references: ok'
