#!/bin/sh
#
# Build the Mirage examples (examples/mirage_*.light) with light build, boot
# each image on solo5-hvt, and check what it does: its console and its exit
# code. The network cases run under solo5-vmnet (macOS 26 or later); a
# server unikernel is fetched from by another one.
#
# Usage: dev/mirage-check.sh [--no-network]
#
# Needs Lightlang built (_build/install/default) and the opam switch
# $LIGHTLANG_MIRAGE_SWITCH (hvf by default) with the MirageOS tools for
# Apple Silicon (solo5-mac). Exits non-zero if a case fails.
#
set -u

HERE="$(cd "$(dirname "$0")/.." && pwd)"
LIGHT="${HERE}/_build/install/default/bin/light"
SWITCH="${LIGHTLANG_MIRAGE_SWITCH:-hvf}"
NETWORK=1
[ "${1:-}" = "--no-network" ] && NETWORK=0

WORK="$(mktemp -d "${TMPDIR:-/tmp}/mirage-check.XXXXXX")"
# the server runs under opam exec and solo5-vmnet: stop solo5-hvt itself
stop_server() {
    pkill -f "solo5-hvt --mem=64 -- ${HERE}/examples/mirage_http_server.hvt"
    pkill -f "solo5-hvt --mem=64 -- ${HERE}/examples/mirage_minimal_web_server.hvt"
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

# build NAME: light build examples/NAME.light, which builds examples/NAME.hvt
build() {
    if "${LIGHT}" build "${HERE}/examples/$1.light" >"${WORK}/build-$1.log" 2>&1; then
        return 0
    fi
    echo "FAIL build $1"
    sed 's/^/    /' "${WORK}/build-$1.log" | tail -15
    FAIL=$((FAIL + 1))
    return 1
}

# run NAME CASE EXPECTED-EXIT PATTERN plain|net [ARGS...]: boot
# examples/NAME.hvt with ARGS (under solo5-vmnet for net; 60 s at most);
# pass if it exits with EXPECTED-EXIT (or is stopped, for "timeout") and
# its console matches the extended regex PATTERN.
run() {
    name="$1" case="$2" expected="$3" pattern="$4" kind="$5"
    shift 5
    limit=60
    [ "${expected}" = "timeout" ] && limit=4
    if [ "${kind}" = net ]; then
        timeout "${limit}" opam exec --switch="${SWITCH}" -- solo5-vmnet -- \
            solo5-hvt --mem=64 -- "${HERE}/examples/${name}.hvt" "$@" \
            >"${WORK}/${case}.log" 2>&1
    else
        timeout "${limit}" opam exec --switch="${SWITCH}" -- \
            solo5-hvt --mem=64 -- "${HERE}/examples/${name}.hvt" "$@" \
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
        hvf solo5-vmnet -- solo5-hvt --mem=64 -- \
            "${HERE}/examples/mirage_http_server.hvt" >"${WORK}/server.log" 2>&1 &
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
                "Hello from Lightlang! You asked for /hello at [0-9:]+ UTC" \
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
            hvf solo5-vmnet -- solo5-hvt --mem=64 -- \
                "${HERE}/examples/mirage_minimal_web_server.hvt" >"${WORK}/web.log" 2>&1 &
            ip2=""
            for _ in $(seq 1 60); do
                ip2="$(grep -o 'Lease obtained! IP: [0-9.]*' "${WORK}/web.log" |
                    head -1 | awk '{print $4}')"
                grep -q "stack assembled" "${WORK}/web.log" && [ -n "${ip2}" ] && break
                sleep 0.25
            done
            run mirage_fetch minimal-web-server 0 "^Hello, web!$" net "--arg=${ip2}"
            pkill -f "solo5-hvt --mem=64 -- ${HERE}/examples/mirage_minimal_web_server.hvt"
        fi
        # nothing listens there: the connection fails, and the fetcher exits 1
        run mirage_fetch fetch-refused 1 "the connection failed" \
            net "--arg=${ip:-192.168.105.1}"
    fi
fi

rm -f "${HERE}"/examples/mirage_*.vo "${HERE}"/examples/mirage_*.glob \
    "${HERE}"/examples/.mirage_*.aux
echo "${PASS} passed, ${FAIL} failed"
[ "${FAIL}" -eq 0 ]
