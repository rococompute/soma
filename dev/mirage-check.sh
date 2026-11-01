#!/bin/sh
#
# Build the Mirage examples (examples/example_files/mirage_*/) with soma build, boot
# each image on solo5-hvt, and check what it does: its console and its exit
# code. The network cases run under solo5-vmnet (macOS 26 or later); a
# server unikernel is fetched from by another one.
#
# Usage: dev/mirage-check.sh [--no-network]
#
# Needs Soma built (_build/install/default) and the opam switch
# $SOMA_MIRAGE_SWITCH (hvf by default) with the MirageOS tools for
# Apple Silicon (solo5-mac). Exits non-zero if a case fails.
#
set -u

HERE="$(cd "$(dirname "$0")/.." && pwd)"
SOMA="${HERE}/_build/install/default/bin/soma"
SWITCH="${SOMA_MIRAGE_SWITCH:-hvf}"
# the memory the images run in, as soma run gives them
MEM="${SOMA_MIRAGE_MEM:-256}"
NETWORK=1
[ "${1:-}" = "--no-network" ] && NETWORK=0

WORK="$(mktemp -d "${TMPDIR:-/tmp}/mirage-check.XXXXXX")"
# the server runs under opam exec and solo5-vmnet: stop solo5-hvt itself
stop_server() {
    pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_http_server/mirage_http_server.hvt"
    pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_minimal_web_server/mirage_minimal_web_server.hvt"
    pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_projects/counter_server/main.hvt"
}
trap 'stop_server 2>/dev/null; rm -rf "${WORK}"' EXIT
PASS=0
FAIL=0

hvf() { opam exec --switch="${SWITCH}" -- "$@"; }

pass() { echo "PASS $1"; PASS=$((PASS + 1)); }
fail() {
    echo "FAIL $1"
    [ -f "${WORK}/$1.log" ] && sed 's/^/    /' "${WORK}/$1.log" | tail -15
    FAIL=$((FAIL + 1))
}

# build NAME: soma build examples/example_files/NAME/NAME.soma, which builds
# examples/example_files/NAME/NAME.hvt
build() {
    if "${SOMA}" build "${HERE}/examples/example_files/$1/$1.soma" >"${WORK}/build-$1.log" 2>&1; then
        return 0
    fi
    echo "FAIL build $1"
    sed 's/^/    /' "${WORK}/build-$1.log" | tail -15
    FAIL=$((FAIL + 1))
    return 1
}

# run NAME CASE EXPECTED-EXIT PATTERN plain|net [ARGS...]: boot
# examples/example_files/NAME/NAME.hvt with ARGS (under solo5-vmnet for net; 60 s at most);
# pass if it exits with EXPECTED-EXIT (or is stopped, for "timeout") and
# its console matches the extended regex PATTERN.
run() {
    name="$1" case="$2" expected="$3" pattern="$4" kind="$5"
    shift 5
    limit=60
    [ "${expected}" = "timeout" ] && limit=4
    if [ "${kind}" = net ]; then
        timeout "${limit}" opam exec --switch="${SWITCH}" -- solo5-vmnet -- \
            solo5-hvt --mem=${MEM} -- "${HERE}/examples/example_files/${name}/${name}.hvt" "$@" \
            >"${WORK}/${case}.log" 2>&1
    else
        timeout "${limit}" opam exec --switch="${SWITCH}" -- \
            solo5-hvt --mem=${MEM} -- "${HERE}/examples/example_files/${name}/${name}.hvt" "$@" \
            >"${WORK}/${case}.log" 2>&1
    fi
    rc=$?
    if [ "${expected}" = "timeout" ]; then ok=$([ ${rc} -eq 124 ] && echo 1)
    else ok=$([ ${rc} -eq "${expected}" ] && echo 1); fi
    if [ -n "${ok}" ] && grep -Eq "${pattern}" "${WORK}/${case}.log"; then
        pass "${case}"
    else
        echo "    (exit ${rc}, expected ${expected})" >>"${WORK}/${case}.log"
        fail "${case}"
    fi
}

build mirage_minimal &&
    run mirage_minimal minimal 0 "^Hello from a unikernel!$" plain

build mirage_hello &&
    run mirage_hello hello 0 "lift off" plain &&
    grep -q "Hello, \[1,2,3\]" "${WORK}/hello.log"

# runs until it is stopped, printing the time every second
build mirage_clock &&
    run mirage_clock clock timeout "^[0-9]{2}:[0-9]{2}:[0-9]{2}$" plain

if [ "${NETWORK}" = 1 ]; then
    if build mirage_http_server && build mirage_fetch; then
        # without an address, the fetcher says how to use it and exits 2
        run mirage_fetch fetch-usage 2 "usage: --arg=ADDRESS" net
        hvf solo5-vmnet -- solo5-hvt --mem=${MEM} -- \
            "${HERE}/examples/example_files/mirage_http_server/mirage_http_server.hvt" >"${WORK}/server.log" 2>&1 &
        server=$!
        ip=""
        for _ in $(seq 1 60); do
            ip="$(grep -o 'Lease obtained! IP: [0-9.]*' "${WORK}/server.log" |
                head -1 | awk '{print $4}')"
            grep -q "serving HTTP" "${WORK}/server.log" && [ -n "${ip}" ] && break
            sleep 0.25
        done
        if [ -z "${ip}" ]; then
            cp "${WORK}/server.log" "${WORK}/http-server.log"
            fail http-server
        else
            run mirage_fetch guest-to-guest 0 \
                "Hello from Soma! You asked for /hello at [0-9:]+ UTC" \
                net "--arg=${ip}"
            if grep -q "request for /hello" "${WORK}/server.log"; then
                pass http-server
            else
                cp "${WORK}/server.log" "${WORK}/http-server.log"
                fail http-server
            fi
        fi
        stop_server
        wait "${server}" 2>/dev/null
        # the minimal web server answers every request with the same page
        if build mirage_minimal_web_server; then
            hvf solo5-vmnet -- solo5-hvt --mem=${MEM} -- \
                "${HERE}/examples/example_files/mirage_minimal_web_server/mirage_minimal_web_server.hvt" >"${WORK}/web.log" 2>&1 &
            ip2=""
            for _ in $(seq 1 60); do
                ip2="$(grep -o 'Lease obtained! IP: [0-9.]*' "${WORK}/web.log" |
                    head -1 | awk '{print $4}')"
                grep -q "stack assembled" "${WORK}/web.log" && [ -n "${ip2}" ] && break
                sleep 0.25
            done
            run mirage_fetch minimal-web-server 0 "^Hello, web!$" net "--arg=${ip2}"
            pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_minimal_web_server/mirage_minimal_web_server.hvt"
        fi
        # nothing listens there: the fetcher says why there is no reply, and
        # exits 1
        run mirage_fetch fetch-refused 1 "the connection was refused|nothing answered within 10 seconds" \
            net "--arg=${ip:-192.168.105.1}"
        # not an IP address: the fetcher says so, and exits 2
        run mirage_fetch fetch-bad-address 2 "not-an-address is not an IP address" \
            net "--arg=not-an-address"
    fi
    # a project as an image: the counter of examples/example_projects/
    # counter_server, asked from the Mac with curl. It starts at the count
    # in the address, or the cookie, or 0; a count that is not a whole
    # number 0 or more is 400.
    COUNTER="${HERE}/examples/example_projects/counter_server"
    if "${SOMA}" build "${COUNTER}/main.soma" >"${WORK}/build-counter.log" 2>&1; then
        hvf solo5-vmnet -- solo5-hvt --mem=${MEM} -- "${COUNTER}/main.hvt" >"${WORK}/counter.log" 2>&1 &
        ip3=""
        for _ in $(seq 1 80); do
            ip3="$(grep -o 'Lease obtained! IP: [0-9.]*' "${WORK}/counter.log" | head -1 | awk '{print $4}')"
            grep -q "serving the counter" "${WORK}/counter.log" && [ -n "${ip3}" ] && break
            sleep 0.25
        done
        jar="${WORK}/cookies"
        ask() { curl -s -m 5 -i -b "${jar}" -c "${jar}" "$@" | tr -d '\r'; }
        if [ -n "${ip3}" ] &&
           ask "http://${ip3}:8080/" | grep -q "<h1>Count: 0</h1>" &&
           ask "http://${ip3}:8080/?count=41" | grep -q 'href="/?count=42"' &&
           ask "http://${ip3}:8080/" | grep -q "<h1>Count: 41</h1>" &&
           ask "http://${ip3}:8080/?count=-1" | grep -q "^HTTP/1.1 400" &&
           curl -s -m 5 -i -H "Cookie: count=1.5" "http://${ip3}:8080/" | grep -q "^HTTP/1.1 400"; then
            pass counter-server
        else
            cp "${WORK}/counter.log" "${WORK}/counter-server.log"
            fail counter-server
        fi
        pkill -f "solo5-hvt --mem=${MEM} -- ${COUNTER}/main.hvt"
    else
        cp "${WORK}/build-counter.log" "${WORK}/counter-server.log"
        fail counter-server
    fi
fi

# WebAssembly modules, called from inside an image: wasm_add's image.soma
# calls add.wasm, built from Rust, with the interpreter in the image; a
# call whose result does not fit its declared type is a failed cast
WASM="${HERE}/examples/example_projects/wasm_add"
if "${SOMA}" run "${WASM}/image.soma" >"${WORK}/wasm.log" 2>&1 &&
   grep -q "^add 2 3 = 5$" "${WORK}/wasm.log" && grep -q "^fib 50 = 12586269025$" "${WORK}/wasm.log" &&
   grep -q "^hypot 3 4 is 5: yes$" "${WORK}/wasm.log" && grep -q "^half 2.5 is 1.25: yes$" "${WORK}/wasm.log"; then
    pass wasm-image
else
    fail wasm-image
fi
printf '%s\n' 'Require Import Sandbox.' 'Import add.' 'main : io unit := print (to_string (add 9223372036854775807 1)).' \
    > "${WASM}/wasm_contract_check.soma"
"${SOMA}" run --events "${WASM}/wasm_contract_check.soma" >"${WORK}/wasm-contract.log" 2>&1
rm -f "${WASM}/wasm_contract_check.soma"
if grep -q '"kind":"cast","message":"expected an N, but got I64 (-9223372036854775808) : i64"' "${WORK}/wasm-contract.log"; then
    pass wasm-contract
else
    fail wasm-contract
fi
rm -rf "${WASM}/.soma-cache"

# soma run says what a run came to, from the image's events
# (toplevel/somaMirage.ml): diagnose CASE PROGRAM PATTERN runs PROGRAM (the
# text of a Soma program) and checks soma run's diagnosis on stderr
diagnose() {
    case="$1"
    printf '%s\n' "$2" > "${WORK}/${case}.soma"
    "${SOMA}" run --events "${WORK}/${case}.soma" >"${WORK}/${case}.log" 2>"${WORK}/${case}.err"
    cat "${WORK}/${case}.err" >> "${WORK}/${case}.log"
    if grep -qE "$3" "${WORK}/${case}.log"; then pass "${case}"; else fail "${case}"; fi
}
diagnose exits 'Require Import Sandbox.
main : io unit := exit 3.' \
    'the program exited with code 3'
diagnose cast_failure 'Require Import Sandbox.
bad (x : Any) : string := x.
main : io unit := print (bad 42).' \
    'soma-outcome \{"outcome":"failed","kind":"cast".*"expected":"a string","actual":"a nat"'
# a failed cast reached through a match into a string (to_string of an
# N) says what it was, not only where it ended up
diagnose cast_through_match 'Require Import Sandbox.
main : io unit := print (to_string ((("41" : string) : Any) : N)).' \
    'the program stopped on a run-time error: expected an N, but got a string'
diagnose stack_overflow 'Require Import Sandbox.
main : io unit := print (to_string (length (repeat 0 (N.to_nat 3000000)))).' \
    'the program stopped on a stack overflow'
SOMA_MIRAGE_MEM=64 diagnose out_of_memory 'Require Import Sandbox.
main : io unit := print (match Pos.iter (cons 0) nil 3000000%positive with nil => "empty" | _ => "built" end).' \
    'the image ran out of memory'
# soma run --supervise runs the image again when its restart policy
# (theories/Soma/Orchestrate.v) says so: out of memory in 64 MB, the
# default policy runs it again with 128, where it finishes
printf '%s\n' 'Require Import Sandbox.
main : io unit := print (match Pos.iter (cons 0) nil 3000000%positive with nil => "empty" | _ => "built" end).' \
    > "${WORK}/supervised.soma"
SOMA_MIRAGE_MEM=64 "${SOMA}" run --supervise "${WORK}/supervised.soma" >"${WORK}/supervised.log" 2>&1
if grep -q "restarting with 128 MB" "${WORK}/supervised.log" && grep -q "^built$" "${WORK}/supervised.log" &&
   grep -q "the restart policy is done, after 1 restart" "${WORK}/supervised.log"; then
    pass supervised
else
    fail supervised
fi

rm -f "${HERE}"/examples/example_files/mirage_*/mirage_*.vo "${HERE}"/examples/example_files/mirage_*/mirage_*.glob \
    "${HERE}"/examples/example_files/mirage_*/.mirage_*.aux
echo "${PASS} passed, ${FAIL} failed"
[ "${FAIL}" -eq 0 ]
