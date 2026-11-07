#!/bin/sh
#
# Build programs that use OCaml modules (toplevel/somaOcaml.ml) and run
# them: an executable, from a module of the project, greet.ml, also from a
# switch made in advance, offline;
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

# a switch made in advance, as a CI image has: given by SOMA_OCAML_SWITCH,
# with a cache of its own and an opam that installs nothing, the program
# builds from what the switch has, at the version soma.toml's [opam] gives
SWITCH="${HOME}/.cache/soma/ocaml"
DUNE_VERSION="$(opam list --switch="${SWITCH}" --installed --short --columns=version dune 2>/dev/null)"
mkdir "${WORK}/ready" "${WORK}/ready/bin" "${WORK}/ready/cache"
cp "${WORK}/greet/greet.ml" "${WORK}/greet/greet.definition" "${WORK}/greet/main.soma" "${WORK}/ready/"
printf '[project]\nname = "ready"\nversion = "0.1.0"\n[opam]\ndune = "%s"\n' "${DUNE_VERSION}" > "${WORK}/ready/soma.toml"
printf '#!/bin/sh\ncase "$1" in install|switch|pin|update) echo "opam $1: refused" >&2; exit 9;; esac\nexec %s "$@"\n' \
    "$(command -v opam)" > "${WORK}/ready/bin/opam"
chmod +x "${WORK}/ready/bin/opam"
if [ -n "${DUNE_VERSION}" ] &&
   PATH="${WORK}/ready/bin:${PATH}" XDG_CACHE_HOME="${WORK}/ready/cache" SOMA_OCAML_SWITCH="${SWITCH}" \
       "${SOMA}" run "${WORK}/ready/main.soma" >"${WORK}/ready.log" 2>&1 &&
   grep -q "^HELLO, SOMA!$" "${WORK}/ready.log" && ! grep -q "refused" "${WORK}/ready.log"; then
    pass ready
else
    fail ready
fi

# A switch opam can't list (another user's, say) is said to be that, not
# taken for an empty one that installing fails on
mkdir "${WORK}/unlisted" "${WORK}/unlisted/bin" "${WORK}/unlisted/cache"
cp "${WORK}/ready/greet.ml" "${WORK}/ready/greet.definition" "${WORK}/ready/main.soma" "${WORK}/ready/soma.toml" "${WORK}/unlisted/"
printf '#!/bin/sh\ncase "$1" in list) echo "Fatal error: open failed on lock: Permission denied" >&2; exit 99;; install) echo "opam install: refused" >&2; exit 9;; esac\nexec %s "$@"\n' \
    "$(command -v opam)" > "${WORK}/unlisted/bin/opam"
chmod +x "${WORK}/unlisted/bin/opam"
if ! PATH="${WORK}/unlisted/bin:${PATH}" XDG_CACHE_HOME="${WORK}/unlisted/cache" SOMA_OCAML_SWITCH="${SWITCH}" \
       "${SOMA}" run "${WORK}/unlisted/main.soma" >"${WORK}/unlisted.log" 2>&1 &&
   grep -q "asking opam what the switch" "${WORK}/unlisted.log" && grep -q "Permission denied" "${WORK}/unlisted.log" &&
   ! grep -q "refused" "${WORK}/unlisted.log"; then
    pass unlisted
else
    fail unlisted
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
