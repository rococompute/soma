#!/usr/bin/env bash
# Sandbox's resolve, https, and names for fetch and connect, through soma
# build --no-image: a program that uses any of them gets a web project
# (net-web: MirageOS's dns-client device, tls-mirage and the NSS
# certificate authorities), which type-checks against the stand-ins; one
# that only serves has no DNS; a misused https fails; and the runtime's HTTP/1.1 framing (requests, and
# answers with a Content-Length, chunked or read to the end) does what it
# should. No solo5 or MirageOS switch, nothing booted, nothing fetched.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
export SOMA_MIRAGE_SWITCH=nonexistent
WEB="$SOMA_MIRAGE_DIR/net-web"
cd "$WORK"

applied() { tr '\n' ' ' < "$2" | grep -Eq "(^|[^A-Za-z0-9_'])$1 +\\("; }

# the example: resolve and https_get make a web project
cp "$ROOT/examples/example_files/mirage_https/mirage_https.soma" .
soma build --no-image mirage_https.soma > web.log 2>&1
grep -q 'net-web (no image)' web.log
[ ! -f mirage_https.hvt ]
[ ! -e "$SOMA_MIRAGE_DIR/net/prog.ml" ]
grep -q 'stackv4v6 @-> dns_client @-> job' "$WEB/config.ml"
grep -q 'generic_dns_client stack happy_eyeballs' "$WEB/config.ml"
grep -q 'main \$ stack \$ dns' "$WEB/config.ml"
for p in tls-mirage ca-certs-nss x509 domain-name; do grep -q "package \"$p\"" "$WEB/config.ml"; done
grep -q 'module Main (S : Tcpip.Stack.V4V6) (D : Dns_client_mirage.S) = struct' "$WEB/unikernel.ml"
grep -q 'let start s dns =' "$WEB/unikernel.ml"
grep -q 'Tls_mirage.Make (S.TCP)' "$WEB/unikernel.ml"
grep -q 'Ca_certs_nss.authenticator' "$WEB/unikernel.ml"
! grep -q 'this image has no resolver' "$WEB/unikernel.ml"
test -f "$WEB/no-image/unikernel.cmo"
grep -Eq "(^|[^A-Za-z0-9_'])Resolve [^o]" "$WEB/prog.ml"
applied Https "$WEB/prog.ml"

# a program that fetches and connects, by name or address, is a web
# image: fetch, connect and connect_within look a name up
rm -rf "$WEB"
DNS="$WEB"
cat > dns_fetch.soma <<'SOMA'
Require Import Sandbox.
From Stdlib Require Import NArith.
main : io unit :=
  r <- fetch "example.org" 80 (http_get "/") ;;
  c <- connect "192.168.64.1" 7 ;;
  d <- connect_within "example.org" 7 500%N ;;
  print "fetched".
SOMA
soma build --no-image dns_fetch.soma > dns.log 2>&1
grep -q '/net-web (no image)' dns.log
grep -q 'stackv4v6 @-> dns_client @-> job' "$DNS/config.ml"
! grep -q 'this image has no resolver' "$DNS/unikernel.ml"
grep -q 'neither an IP address nor a host name' "$DNS/unikernel.ml"
test -f "$DNS/no-image/unikernel.cmo"

# a program that only serves has no DNS
cat > serve_only.soma <<'SOMA'
Require Import Sandbox.
main : io unit := serve 8080 (fun _ => ret "hi").
SOMA
soma build --no-image serve_only.soma > serve.log 2>&1
grep -q '/net (no image)' serve.log
! grep -q dns_client "$SOMA_MIRAGE_DIR/net/config.ml"
grep -q 'this image has no resolver' "$SOMA_MIRAGE_DIR/net/unikernel.ml"

# with storage too: the stack, then DNS, then the disk
cat > web_storage.soma <<'SOMA'
Require Import Sandbox.
main : io unit := r <- resolve "mirageos.org" ;; write_file "seen" "yes".
SOMA
soma build --no-image web_storage.soma > storage.log 2>&1
grep -q 'net-web-storage (no image)' storage.log
grep -q 'stackv4v6 @-> dns_client @-> block @-> job' "$SOMA_MIRAGE_DIR/net-web-storage/config.ml"
grep -q 'main \$ stack \$ dns \$ storage' "$SOMA_MIRAGE_DIR/net-web-storage/config.ml"
grep -q 'let start s dns disk =' "$SOMA_MIRAGE_DIR/net-web-storage/unikernel.ml"

# https misused: headers are pairs of strings, not a number
cat > misused.soma <<'SOMA'
Require Import Sandbox.
main : io unit := a <- https "GET" "mirageos.org" 443 "/" 7 "" ;; print "asked".
SOMA
if soma build --no-image misused.soma > misused.log 2>&1; then
    echo 'https with a number for its headers passed the check' >&2
    exit 1
fi

# the runtime's HTTP/1.1 framing, as generated, run by OCaml
sed -n '/^let has_line_break/,/^(\* Links (Sandbox/p' "$WEB/soma_rt.ml" | sed '$d' > framing.ml
cat >> framing.ml <<'ML'
let () =
  let ok = function Ok x -> x | Error e -> failwith e in
  let req = ok (http_request "GET" "mempool.space" 443 "/api/blocks/tip/height" [("Accept", "text/plain")] "") in
  assert (req = "GET /api/blocks/tip/height HTTP/1.1\r\nHost: mempool.space\r\nConnection: close\r\nAccept: text/plain\r\nUser-Agent: soma\r\n\r\n");
  let post = ok (http_request "POST" "example.org" 8443 "" [("Host", "evil"); ("content-type", "text/plain")] "abc") in
  assert (post = "POST / HTTP/1.1\r\nHost: example.org:8443\r\nConnection: close\r\nContent-Length: 3\r\ncontent-type: text/plain\r\nUser-Agent: soma\r\n\r\nabc");
  assert (Result.is_error (http_request "GET" "a.org" 443 "/" [("X", "1\r\nInjected: yes")] ""));
  assert (Result.is_error (http_request "GET" "a.org" 443 "/ HTTP/1.0" [] ""));
  let st, hs, body = ok (http_answer "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 6\r\n\r\n843210extra") in
  assert (st = 200 && body = "843210" && List.assoc "content-type" hs = "text/plain");
  let _, _, body = ok (http_answer "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n4\r\nWiki\r\n6;x=y\r\npedia \r\n0\r\n\r\n") in
  assert (body = "Wikipedia ");
  let st, _, body = ok (http_answer "HTTP/1.0 404 Not Found\r\n\r\nno such page") in
  assert (st = 404 && body = "no such page");
  assert (Result.is_error (http_answer ""));
  assert (Result.is_error (http_answer "garbage"));
  assert (Result.is_error (http_answer "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nshort"));
  assert (Result.is_error (http_answer "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nzz\r\n"));
  print_endline "framing ok"
ML
if command -v ocaml >/dev/null 2>&1; then ocaml framing.ml > framing.log 2>&1; grep -q 'framing ok' framing.log
else echo "no ocaml on PATH: the framing isn't run"; fi
echo "soma_web: ok"
