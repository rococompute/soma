#!/usr/bin/env bash
# Returning state-machine loops in the generated backend, with real Lwt.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 60 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cp "$ROOT/examples/example_files/mirage_loop/mirage_loop.soma" "$WORK/main.soma"
cd "$WORK"
soma build --no-image main.soma > build.log 2>&1
P="$SOMA_MIRAGE_DIR/plain"
grep -q 'loop_step' "$P/prog.mli"
if command -v ocamlfind >/dev/null && ocamlfind query lwt >/dev/null 2>&1; then
    OCAMLC=(ocamlfind ocamlc -package lwt -linkpkg)
else
    echo 'loop: runtime tests require ocamlfind lwt' >&2; exit 1
fi
cp "$P"/{prog.ml,prog.mli,uint63.ml,soma_word64.ml,soma_handles.ml,float64.ml} .
python3 - "$P/soma_rt.ml" > runtime.ml <<'PY'
import re, sys
text = open(sys.argv[1]).read()
print('open Lwt.Infix\nlet check = Prog.Gradual_rt.check')
print("let rec run : 'a. unit -> 'a Prog.io -> 'a Lwt.t = fun net m -> match check m with")
for name in ('Ret', 'Bind', 'Await_promise', 'Loop', 'Throw_exception'):
    start = text.index('  | Prog.' + name + ' ')
    end = start + 1 + re.search(r'^  \| Prog\.', text[start+1:], re.M).start()
    print(text[start:end])
print('  | _ -> failwith "unexpected effect in loop runtime test"')
PY
cp "$ROOT/test-suite/misc/soma_loop_runtime.ml" check.ml
"${OCAMLC[@]}" -w -a -c uint63.ml soma_word64.ml soma_handles.ml float64.ml prog.mli prog.ml runtime.ml check.ml > compile.log 2>&1
"${OCAMLC[@]}" -o check uint63.cmo soma_word64.cmo soma_handles.cmo float64.cmo prog.cmo runtime.cmo check.cmo >> compile.log 2>&1
./check
if [ "${SOMA_TEST_HVF:-0}" = 1 ]; then
    soma build main.soma > image.log 2>&1
    timeout 20 opam exec --switch="${SOMA_MIRAGE_SWITCH:-hvf}" -- solo5-hvt --mem=256 -- main.hvt > boot.log 2>&1
    grep -q 'returning loops, context, failure and cancellation verified' boot.log
fi
echo 'loop: ok'
