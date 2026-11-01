#!/bin/sh
#
# Build programs that use OCaml modules (toplevel/somaOcaml.ml) and run
# them: an executable, from a module of the project, greet.ml;
# examples/example_projects/async_tasks, an executable that calls Async;
# and examples/example_projects/bonsai_counter, a page that Bonsai runs,
# served by soma run and clicked in headless Chrome (dev/page-clicks.mjs).
#
# Usage: dev/ocaml-check.sh
#
# Needs Soma built (_build/install/default), opam, Node 22 or later and
# Chrome. The first run installs Async and Bonsai into Soma's opam switch
# (~/.cache/soma/ocaml), which takes a while. Exits non-zero if a case fails.
#
set -u

HERE="$(cd "$(dirname "$0")/.." && pwd)"
SOMA="${HERE}/_build/install/default/bin/soma"
PORT="${SOMA_PORT:-8790}"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/ocaml-check.XXXXXX")"
trap 'kill ${SERVER:-} 2>/dev/null; rm -rf "${WORK}"' EXIT
PASS=0
FAIL=0

pass() { echo "PASS $1"; PASS=$((PASS + 1)); }
fail() {
    echo "FAIL $1"
    [ -f "${WORK}/$1.log" ] && sed 's/^/    /' "${WORK}/$1.log" | tail -15
    FAIL=$((FAIL + 1))
}

# an executable: greet.ml, declared by greet.definition
mkdir "${WORK}/greet"
cat > "${WORK}/greet/greet.ml" <<'EOT'
type greeting = string
let hello name = "Hello, " ^ name ^ "!"
let shout (g : greeting) = String.uppercase_ascii g
let say g = print_endline g
EOT
cat > "${WORK}/greet/greet.definition" <<'EOT'
greeting : Type.
hello : string -> greeting.
shout : greeting -> greeting.
say : greeting -> unit.
EOT
printf '%s\n' 'Import greet.' 'main := say (shout (hello "Soma")).' > "${WORK}/greet/main.soma"
if "${SOMA}" run "${WORK}/greet/main.soma" >"${WORK}/executable.log" 2>&1 &&
   grep -q "^HELLO, SOMA!$" "${WORK}/executable.log"; then
    pass executable
else
    fail executable
fi

# Async: three tasks at once, done in the order of their times, which is
# the one Soma computes
TASKS="${HERE}/examples/example_projects/async_tasks"
if "${SOMA}" run "${TASKS}/main.soma" >"${WORK}/async.log" 2>&1 &&
   [ "$(grep -v '^Compiling ' "${WORK}/async.log" | tr '\n' ' ')" = "fast is done medium is done slow is done all done " ]; then
    pass async
else
    fail async
fi

# soma extract: Async's program as an OCaml project, built by dune alone,
# in Soma's switch, where async and core are
if "${SOMA}" extract "${TASKS}/main.soma" -o "${WORK}/tasks-ocaml" >"${WORK}/extract.log" 2>&1 &&
   (cd "${WORK}/tasks-ocaml" && opam exec --switch="${HOME}/.cache/soma/ocaml" -- \
        dune build --profile release) >>"${WORK}/extract.log" 2>&1 &&
   [ "$("${WORK}/tasks-ocaml/_build/default/soma_main.exe" | tr '\n' ' ')" = "fast is done medium is done slow is done all done " ]; then
    pass extract
else
    fail extract
fi

# a page: the counter, served, clicked +, +, +, -, then + until its limit, then reset
COUNTER="${HERE}/examples/example_projects/bonsai_counter"
SOMA_PORT=${PORT} "${SOMA}" run "${COUNTER}/main.soma" >"${WORK}/page.log" 2>&1 &
SERVER=$!
for _ in $(seq 1 600); do
    grep -q "^Serving " "${WORK}/page.log" && break
    kill -0 ${SERVER} 2>/dev/null || break
    sleep 1
done
URL="$(sed -n 's/^Serving .* at \(http[^ ]*\) .*/\1/p' "${WORK}/page.log")"
if [ -n "${URL}" ] &&
   node "${HERE}/dev/page-clicks.mjs" "${URL}" "0,0,0,1,0,0,0,0,0,0,0,0,0,2" >>"${WORK}/page.log" 2>&1 &&
   grep -q "^Count: 0 of at most 10 | Count: 1 of at most 10 | Count: 2 of at most 10 | Count: 3 of at most 10 | Count: 2 of at most 10 | Count: 3 of at most 10 | Count: 4 of at most 10 | Count: 5 of at most 10 | Count: 6 of at most 10 | Count: 7 of at most 10 | Count: 8 of at most 10 | Count: 9 of at most 10 | Count: 10 of at most 10 | Count: 10 of at most 10 | Count: 0 of at most 10$" "${WORK}/page.log"; then
    pass page
else
    fail page
fi
kill -INT ${SERVER} 2>/dev/null
wait ${SERVER} 2>/dev/null

echo "${PASS} passed, ${FAIL} failed"
[ "${FAIL}" -eq 0 ]
