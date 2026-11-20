#!/usr/bin/env bash
# Exercise the exact Unix socket shim under backpressure, using the proved
# HostSpec advancement function to account for every acknowledged byte.
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export XDG_CACHE_HOME="$WORK/cache"
cd "$WORK"
printf 'OCaml Library "unix".\ncheck : (string -> nat -> option (string * string)) -> string.\n' > driver.definition
# the project's own Soma_host (soma_host.ml and its C), which main's use
# of Host.print_lines puts in it
cat > driver.ml <<'OCAML'
module Host = Soma_host
let check advance =
  let left, right = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.set_nonblock left; Unix.set_nonblock right;
  Unix.setsockopt_int left Unix.SO_SNDBUF 4096;
  let sender = Host.sock_add left and receiver = Host.sock_add right in
  let payload = String.init 1048576 (fun i -> Char.chr ((i * 71) land 255)) in
  let pending = ref payload and received = Buffer.create 1048576 in
  let retries = ref 0 and partial = ref 0 and steps = ref 0 in
  let drain () = match Host.sock_read receiver with
    | true, (_, ["bytes"; bytes]) -> Buffer.add_string received bytes
    | true, (_, ["again"]) -> ()
    | _ -> assert false in
  while !pending <> "" do
    incr steps; assert (!steps < 100000);
    match Host.sock_write sender !pending with
    | true, (_, ["wrote"; count]) ->
        let count = int_of_string count in
        if count < String.length !pending then incr partial;
        (match advance !pending count with
         | Some (sent, kept) ->
             assert (sent ^ kept = !pending && String.length sent = count);
             pending := kept
         | None -> assert false)
    | true, (_, ["again"]) -> incr retries; drain ()
    | _ -> assert false
  done;
  while Buffer.length received < String.length payload do drain () done;
  assert (!partial > 0 && !retries > 0);
  assert (Buffer.contents received = payload);
  ignore (Host.sock_close sender); ignore (Host.sock_close receiver);
  "PASS actual host partial writes and retries preserve all bytes under backpressure"
OCAML
cat > main.soma <<'SOMA'
Require Import Soma.HostSpec.
Require Soma.Host.
Import driver.
main : unit := Host.print_lines [check SocketWrites.advance].
SOMA
soma run main.soma > run.log 2>&1 || { cat run.log; exit 1; }
cat run.log
grep -q '^PASS actual host partial writes' run.log
