#!/bin/sh
#
# Build the Mirage examples (examples/example_files/mirage_*/) with soma build, boot
# each image on solo5-hvt, and check what it does: its console and its exit
# code. The network cases run under solo5-vmnet (macOS 26 or later); a
# server unikernel is fetched from by another one, and one fetches a page
# over HTTPS from the internet (outbound access needed).
#
# Usage: dev/mirage-check.sh [--no-network | --no-image | --storage-only]
#
# Needs Soma built (_build/install/default). Image builds need the opam
# switch $SOMA_MIRAGE_SWITCH (hvf by default) with the MirageOS tools for
# Apple Silicon (solo5-mac). --no-image does not boot and needs neither
# solo5 nor that switch: it runs soma build --no-image on each Sandbox
# example and on one program that misuses an io result. Exits non-zero
# if a case fails.
#
set -u

HERE="$(cd "$(dirname "$0")/.." && pwd)"
SOMA="${HERE}/_build/install/default/bin/soma"
SWITCH="${SOMA_MIRAGE_SWITCH:-hvf}"
export SOMA_MIRAGE_SWITCH="${SWITCH}"
# the memory the images run in, as soma run gives them
MEM="${SOMA_MIRAGE_MEM:-256}"
NETWORK=1
NO_IMAGE=0
STORAGE_ONLY=0
if [ "${1:-}" = "--no-image" ]; then
  NO_IMAGE=1
elif [ "${1:-}" = "--no-network" ]; then
  NETWORK=0
elif [ "${1:-}" = "--storage-only" ]; then
  NETWORK=0
  STORAGE_ONLY=1
fi

WORK="$(mktemp -d "${TMPDIR:-/tmp}/mirage-check.XXXXXX")"
# the server runs under opam exec and solo5-vmnet: stop solo5-hvt itself
stop_server() {
    pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_http_server/mirage_http_server.hvt"
    pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_minimal_web_server/mirage_minimal_web_server.hvt"
    pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_projects/counter_server/main.hvt"
    pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_link_server/mirage_link_server.hvt"
    pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_frame_server/mirage_frame_server.hvt"
    pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_raw_link/mirage_raw_link.hvt"
    pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_events/mirage_events.hvt"
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

# soma build --no-image NAME's file. No image, no switch: the log says so.
no_image_one() {
    name="$1"
    file="$2"
    if "${SOMA}" build --no-image "${file}" >"${WORK}/${name}.log" 2>&1 &&
       grep -q '(no image)' "${WORK}/${name}.log"; then
        pass "${name}"
    else
        fail "${name}"
    fi
}

if [ "${NO_IMAGE}" = 1 ]; then
    for example in mirage_minimal mirage_hello mirage_clock mirage_milliseconds mirage_raw_clock mirage_crypto mirage_fetch mirage_http_server \
        mirage_minimal_web_server mirage_link_client mirage_link_server mirage_raw_link mirage_events \
        mirage_frame_client mirage_frame_server mirage_mailbox mirage_supervised mirage_storage_model mirage_storage \
        mirage_https; do
        no_image_one "no-image-${example}" "${HERE}/examples/example_files/${example}/${example}.soma"
    done
    no_image_one "no-image-counter" "${HERE}/examples/example_projects/counter_server/main.soma"
    no_image_one "no-image-wasm" "${HERE}/examples/example_projects/wasm_add/image.soma"
    # print expects a string; fetch returns fetched
    printf '%s\n' 'Require Import Sandbox.' \
        'main : io unit := r <- fetch "127.0.0.1" 9 (http_get "/") ;; print r.' \
        > "${WORK}/illtyped.soma"
    if "${SOMA}" build --no-image "${WORK}/illtyped.soma" >"${WORK}/no-image-illtyped.log" 2>&1; then
        echo "FAIL no-image-illtyped"
        echo "    expected a type error" >>"${WORK}/no-image-illtyped.log"
        FAIL=$((FAIL + 1))
    elif grep -q 'Error' "${WORK}/no-image-illtyped.log"; then
        pass "no-image-illtyped"
    else
        fail "no-image-illtyped"
    fi
else
# Boot three times with one dedicated zeroed disk: each image checks exact
# file contents from its predecessor, including replacement and ordered appends.
# The disk argument belongs before solo5's --. Finally check a fresh disk.
if build mirage_storage; then
    truncate -s 8M "${WORK}/storage.img"
    for boot in 1 2 3 fresh; do
        expected_boot="${boot}"
        if [ "${boot}" = fresh ]; then
            # A different disk starts empty even after the image has booted.
            rm "${WORK}/storage.img"
            truncate -s 8M "${WORK}/storage.img"
            expected_boot=1
        fi
        if timeout 60 opam exec --switch="${SWITCH}" -- solo5-hvt --mem=${MEM} \
            --block:storage="${WORK}/storage.img" -- \
            "${HERE}/examples/example_files/mirage_storage/mirage_storage.hvt" \
            >"${WORK}/storage-${boot}.log" 2>&1 &&
           grep -qx "boot ${expected_boot}" "${WORK}/storage-${boot}.log" &&
           grep -qx "storage checks passed" "${WORK}/storage-${boot}.log"; then
            pass "storage-${boot}"
        else
            fail "storage-${boot}"
        fi
    done
fi
if [ "${STORAGE_ONLY}" = 0 ]; then
build mirage_minimal &&
    run mirage_minimal minimal 0 "^Hello from a unikernel!$" plain

build mirage_hello &&
    run mirage_hello hello 0 "lift off" plain &&
    grep -q "Hello, \[1,2,3\]" "${WORK}/hello.log"

build mirage_milliseconds &&
    run mirage_milliseconds milliseconds 0 "^elapsed at least 1000 ms$" plain

# write without line breaks, random bytes, nanoseconds, the wall clock
build mirage_raw_clock &&
    run mirage_raw_clock raw-clock 0 "^random bytes, nanoseconds and the wall clock as expected$" plain &&
    grep -q "^raw: ok$" "${WORK}/raw-clock.log"
# Soma.Crypto in an image: SHA-256, and a 2048-bit RSA signature that
# Pantheon's shell.ml made of a transaction, verified; a changed one refused
build mirage_crypto &&
    run mirage_crypto crypto 0 "^verified a Pantheon transaction's signature$" plain &&
    run mirage_crypto crypto-refused 0 "^refused a changed transaction$" plain

# runs until it is stopped, printing the time every second
build mirage_clock &&
    run mirage_clock clock timeout "^[0-9]{2}:[0-9]{2}:[0-9]{2}$" plain

if [ "${NETWORK}" = 1 ]; then
    # resolve and https: DNS, TCP and TLS to the internet through vmnet's
    # NAT, the server's certificate checked against the NSS authorities
    if build mirage_https; then
        run mirage_https https 0 "^https://mirageos.org/: status 200, [1-9][0-9]* bytes" net
        run mirage_https https-untrusted 1 \
            "^no answer: TLS with self-signed.badssl.com: authentication failure" net "--arg=self-signed.badssl.com"
    fi
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
    # links that stay open: the link client connects to the link server,
    # they exchange lines on one connection, and the client notices when the
    # server closes it after "bye"; once the server is stopped, connecting is
    # refused (or times out)
    if build mirage_link_server && build mirage_link_client; then
        run mirage_link_client link-usage 2 "usage: --arg=ADDRESS" net
        run mirage_link_client link-bad-address 2 "not-an-address is not an IP address" \
            net "--arg=not-an-address"
        hvf solo5-vmnet -- solo5-hvt --mem=${MEM} -- \
            "${HERE}/examples/example_files/mirage_link_server/mirage_link_server.hvt" >"${WORK}/link.log" 2>&1 &
        link_server=$!
        ip4=""
        for _ in $(seq 1 60); do
            ip4="$(grep -o 'Lease obtained! IP: [0-9.]*' "${WORK}/link.log" |
                head -1 | awk '{print $4}')"
            grep -q "listening for links on port 7000" "${WORK}/link.log" && [ -n "${ip4}" ] && break
            sleep 0.25
        done
        if [ -z "${ip4}" ]; then
            cp "${WORK}/link.log" "${WORK}/link-server.log"
            fail link-server
        else
            run mirage_link_client link-exchange 0 "the link went as expected" net "--arg=${ip4}"
            if grep -q "^server: hello from the link server$" "${WORK}/link-exchange.log" &&
               grep -q "^server: echo: one$" "${WORK}/link-exchange.log" &&
               grep -q "^server: echo: two$" "${WORK}/link-exchange.log" &&
               grep -q "^server: bye$" "${WORK}/link-exchange.log" &&
               grep -q "^the server closed the connection$" "${WORK}/link-exchange.log"; then
                pass link-lines
            else
                cp "${WORK}/link-exchange.log" "${WORK}/link-lines.log"
                fail link-lines
            fi
            # the client has exited, so the server has its lines
            if grep -q "^got one$" "${WORK}/link.log" && grep -q "^got bye$" "${WORK}/link.log"; then
                pass link-server
            else
                cp "${WORK}/link.log" "${WORK}/link-server.log"
                fail link-server
            fi
        fi
        pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_link_server/mirage_link_server.hvt"
        wait "${link_server}" 2>/dev/null
        # nothing listens on the link port of the stopped server
        run mirage_link_client link-refused 1 "the connection was refused|nothing answered within 10 seconds" \
            net "--arg=${ip4:-192.168.105.1}"
    fi
    # length-prefixed frames: the frame client connects to the frame
    # server, they exchange frames on one connection (an empty one, and one
    # of two lines), and the client notices when the server closes it after
    # "bye"
    if build mirage_frame_server && build mirage_frame_client; then
        run mirage_frame_client frame-usage 2 "usage: --arg=ADDRESS" net
        hvf solo5-vmnet -- solo5-hvt --mem=${MEM} -- \
            "${HERE}/examples/example_files/mirage_frame_server/mirage_frame_server.hvt" >"${WORK}/frame.log" 2>&1 &
        frame_server=$!
        ip5=""
        for _ in $(seq 1 60); do
            ip5="$(grep -o 'Lease obtained! IP: [0-9.]*' "${WORK}/frame.log" |
                head -1 | awk '{print $4}')"
            grep -q "listening for frames on port 7001" "${WORK}/frame.log" && [ -n "${ip5}" ] && break
            sleep 0.25
        done
        if [ -z "${ip5}" ]; then
            cp "${WORK}/frame.log" "${WORK}/frame-server.log"
            fail frame-server
        else
            run mirage_frame_client frame-exchange 0 "the frames went as expected" net "--arg=${ip5}"
            if grep -q "^server: hello from the frame server$" "${WORK}/frame-exchange.log" &&
               grep -q "^server: echo: one$" "${WORK}/frame-exchange.log" &&
               grep -q "^server: echo: first line$" "${WORK}/frame-exchange.log" &&
               grep -q "^second line$" "${WORK}/frame-exchange.log" &&
               grep -q "^server: bye$" "${WORK}/frame-exchange.log" &&
               grep -q "^the server closed the connection$" "${WORK}/frame-exchange.log"; then
                pass frame-messages
            else
                cp "${WORK}/frame-exchange.log" "${WORK}/frame-messages.log"
                fail frame-messages
            fi
            # the client has exited, so the server has its frames
            if grep -q "^got frame: one$" "${WORK}/frame.log" && grep -q "^got frame: bye$" "${WORK}/frame.log"; then
                pass frame-server
            else
                cp "${WORK}/frame.log" "${WORK}/frame-server.log"
                fail frame-server
            fi
        fi
        pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_frame_server/mirage_frame_server.hvt"
        wait "${frame_server}" 2>/dev/null
    fi
    # raw bytes: mirage_raw_link as a server, and again as its client,
    # which sends "abc" with no line break and expects "got abc", then
    # "idle" when the server's receive times out
    if build mirage_raw_link; then
        hvf solo5-vmnet -- solo5-hvt --mem=${MEM} -- \
            "${HERE}/examples/example_files/mirage_raw_link/mirage_raw_link.hvt" >"${WORK}/raw.log" 2>&1 &
        raw_server=$!
        ip7=""
        for _ in $(seq 1 60); do
            ip7="$(grep -o 'Lease obtained! IP: [0-9.]*' "${WORK}/raw.log" | head -1 | awk '{print $4}')"
            grep -q "raw link on port 7003" "${WORK}/raw.log" && [ -n "${ip7}" ] && break
            sleep 0.25
        done
        if [ -z "${ip7}" ]; then
            cp "${WORK}/raw.log" "${WORK}/raw-server.log"
            fail raw-server
        else
            run mirage_raw_link raw-client 0 "^the raw link went as expected$" net "--arg=${ip7}"
            if grep -q "^address: ${ip7}$" "${WORK}/raw.log" && grep -q "^chunk: abc$" "${WORK}/raw.log" &&
               grep -q "^nothing for a second$" "${WORK}/raw.log"; then
                pass raw-server
            else
                cp "${WORK}/raw.log" "${WORK}/raw-server.log"
                fail raw-server
            fi
        fi
        kill "${raw_server}" 2>/dev/null
        pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_raw_link/mirage_raw_link.hvt"
        wait "${raw_server}" 2>/dev/null
    fi
    # a select over everything: mirage_events as a server (UDP pongs, TCP
    # greetings), and as its client, quiet, whose one loop sees a timer,
    # the pong, and a watched connection's bytes and end
    if build mirage_events; then
        hvf solo5-vmnet -- solo5-hvt --mem=${MEM} -- \
            "${HERE}/examples/example_files/mirage_events/mirage_events.hvt" >"${WORK}/events.log" 2>&1 &
        events_server=$!
        ip8=""
        for _ in $(seq 1 60); do
            ip8="$(grep -o 'Lease obtained! IP: [0-9.]*' "${WORK}/events.log" | head -1 | awk '{print $4}')"
            grep -q "events server on ports 7004 and 7005" "${WORK}/events.log" && [ -n "${ip8}" ] && break
            sleep 0.25
        done
        if [ -z "${ip8}" ]; then
            cp "${WORK}/events.log" "${WORK}/events-server.log"
            fail events-server
        else
            run mirage_events events-client 0 "^all four came$" net "--arg=${ip8}" --soma-quiet
            if grep -q "^select 0: nothing yet$" "${WORK}/events-client.log" &&
               grep -q "^datagram: pong ping$" "${WORK}/events-client.log" &&
               grep -q "^bytes: hello$" "${WORK}/events-client.log" &&
               grep -q "^timer$" "${WORK}/events-client.log" &&
               ! grep -q "soma-event" "${WORK}/events-client.log"; then
                pass events-quiet
            else
                cp "${WORK}/events-client.log" "${WORK}/events-quiet.log"
                fail events-quiet
            fi
        fi
        kill "${events_server}" 2>/dev/null
        pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_events/mirage_events.hvt"
        wait "${events_server}" 2>/dev/null
    fi
    # a select over connections: the mailbox image prints what two
    # connections from the Mac did, in order, and exits after their ends
    if build mirage_mailbox; then
        hvf solo5-vmnet -- solo5-hvt --mem=${MEM} -- \
            "${HERE}/examples/example_files/mirage_mailbox/mirage_mailbox.hvt" >"${WORK}/mailbox.log" 2>&1 &
        mailbox_image=$!
        ip6=""
        for _ in $(seq 1 60); do
            ip6="$(grep -o 'Lease obtained! IP: [0-9.]*' "${WORK}/mailbox.log" |
                head -1 | awk '{print $4}')"
            grep -q "mailbox on port 7002" "${WORK}/mailbox.log" && [ -n "${ip6}" ] && break
            sleep 0.25
        done
        if [ -z "${ip6}" ]; then
            fail mailbox
        else
            printf 'one\n' | nc -w 2 "${ip6}" 7002 >/dev/null 2>&1
            printf 'two\n' | nc -w 2 "${ip6}" 7002 >/dev/null 2>&1
            for _ in $(seq 1 20); do grep -q "two connections ended" "${WORK}/mailbox.log" && break; sleep 0.25; done
            if grep -q "^mail: opened from " "${WORK}/mailbox.log" &&
               grep -q "^mail: bytes one$" "${WORK}/mailbox.log" &&
               grep -q "^mail: bytes two$" "${WORK}/mailbox.log" &&
               [ "$(grep -c '^mail: closed$' "${WORK}/mailbox.log")" -eq 2 ] &&
               grep -q "^two connections ended$" "${WORK}/mailbox.log"; then
                pass mailbox
            else
                fail mailbox
            fi
        fi
        kill "${mailbox_image}" 2>/dev/null
        pkill -f "solo5-hvt --mem=${MEM} -- ${HERE}/examples/example_files/mirage_mailbox/mirage_mailbox.hvt"
        wait "${mailbox_image}" 2>/dev/null
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
# a recursion deeper than the stack (nat is an OCaml int in an image, so
# it is the depth that overflows, not a unary number)
diagnose stack_overflow 'Require Import Sandbox.
Fixpoint deep (n : nat) : nat := match n with O => O | S k => S (deep k) end.
main : io unit := print (to_string (deep (N.to_nat 200000000))).' \
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
fi
fi

rm -f "${HERE}"/examples/example_files/mirage_*/mirage_*.vo "${HERE}"/examples/example_files/mirage_*/mirage_*.glob \
    "${HERE}"/examples/example_files/mirage_*/.mirage_*.aux
echo "${PASS} passed, ${FAIL} failed"
[ "${FAIL}" -eq 0 ]
