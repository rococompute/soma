#!/usr/bin/env bash
# Check the public types, then run the generated TCP adapter against controlled
# reads/writes using real Lwt. No sockets, timers, VMs or model requests.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 50 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cd "$WORK"
cp "$ROOT/examples/example_files/mirage_tcp_errors/mirage_tcp_errors.soma" main.soma
soma build --no-image main.soma > build.log 2>&1
cat > server.soma <<'SOMA'
Require Import Sandbox.
talk (c : connection) : io unit :=
  _ <- send_checked c "hello" ;; _ <- receive_checked c 1%N ;; ret tt.
main : io unit := listen 7001 talk.
SOMA
soma build --no-image server.soma > server.log 2>&1
P="$SOMA_MIRAGE_DIR/net"
cp "$P"/{prog.ml,prog.mli,uint63.ml,soma_word64.ml,float64.ml} .
cp "$P/no-image/soma_handles.ml" .
LWT_FILES=()
if command -v ocamlfind >/dev/null && ocamlfind query lwt >/dev/null 2>&1; then
    OCAMLC=(ocamlfind ocamlc -package lwt -linkpkg)
elif [ -n "${LWT_SOURCE:-}" ]; then
    # Use a locally vendored Lwt core without changing any opam switch.
    for name in lwt_sequence lwt_rte lwt lwt_mutex lwt_condition; do
        cp "$LWT_SOURCE/$name.mli" .
        src="$LWT_SOURCE/$name.ml"
        [ "$name" != lwt_rte ] || src="$LWT_SOURCE/lwt_rte.without.ml"
        cp "$src" "$name.ml"
        ocamlc -w -a -c "$name.mli" "$name.ml" >> compile.log 2>&1
        LWT_FILES+=("$name.cmo")
    done
    OCAMLC=(ocamlc)
else
    echo 'tcp errors: contracts ok; runtime tests require ocamlfind lwt or LWT_SOURCE (vendored lwt/src/core)'
    exit 0
fi
python3 - "$P/soma_rt.ml" "$P/unikernel.ml" > links.ml <<'PY'
import sys
runtime, network = (open(p).read() for p in sys.argv[1:])
types = runtime[runtime.index('type link ='):runtime.index('(* Framing, as Soma.Wire')]
framing = runtime[runtime.index('let take_line = Prog.soma_wire_take_line'):runtime.index('(* What the network provides')]
link_type = network[network.index('  type link ='):network.index('  let start ')]
start = network.index('    let links = Hashtbl.create 7')
end = network.index('    Soma_rt.main ~network:true', start)
print('''open Lwt.Infix
module Cstruct = struct let of_string x = x let to_string x = x end
module Ipaddr = struct
  type t = V4 of string | V6 of string
  let of_string s = Ok (V4 s)
  let to_string = function V4 s | V6 s -> s
  module V4 = struct let to_string s = s end
  module Prefix = struct let address x = x end
end
module Soma_rt = struct
  type field = I of int | B of bool | S of string
  let event _ _ = ()
  let report ~during:_ _ = ()
  let open_connections = ref 0
  let served = ref 0
''' + types + framing + '''
  let incoming : incoming Queue.t = Queue.create ()
  let post_incoming e = Queue.add e incoming
end
module Duration = struct let of_sec s = s end
module Mirage_sleep = struct let ns _ = fst (Lwt.wait ()) end
module S = struct
  module TCP = struct
    type error = [ `Reset ]
    type write_error = [ `Closed ]
    type response = ([ `Data of string | `Eof ], error) result
    type flow = { reads : response Lwt.t Queue.t; mutable closed : int;
      mutable writes_fail : bool; mutable read_count : int }
    let pp_error fmt `Reset = Format.pp_print_string fmt "connection reset"
    let pp_write_error fmt `Closed = Format.pp_print_string fmt "write closed"
    let close f = f.closed <- f.closed + 1; Lwt.return_unit
    let read f = f.read_count <- f.read_count + 1;
      if Queue.is_empty f.reads then fst (Lwt.wait ()) else Queue.take f.reads
    let write f _ = Lwt.return (if f.writes_fail then Error `Closed else Ok ())
    let handler : (flow -> unit Lwt.t) option ref = ref None
    let listen _ ~port:_ h = handler := Some h
    let dst _ = (Ipaddr.V4 "192.0.2.7",1234)
  end
  module IP = struct let configured_ips _ = [] end
  module UDP = struct
    let listen _ ~port:_ _ = ()
    let write ?src_port:_ ~dst:_ ~dst_port:_ _ _ = Lwt.return (Ok ())
  end
  let tcp s = s
  let ip s = s
  let udp s = s
end
''' + link_type + '''
type api = {
  register : S.TCP.flow -> int;
  send : int -> string -> Soma_rt.transmission Lwt.t;
  receive : int -> (unit -> unit Lwt.t) option -> Soma_rt.raw Lwt.t;
  receive_line : int -> string option Lwt.t;
  receive_frame : int -> int -> int -> Soma_rt.frame Lwt.t;
  close : int -> unit Lwt.t;
  watch : int -> unit;
  listen_mailbox : int -> unit;
}
let make () =
  let s = () in
  let servers = ref 0 in
  let dial _ _ = Lwt.return `Refused in
  let dial_within _ _ _ = Lwt.return `Refused in
  let ip_of s = Lwt.return (Ok s) in
  let unresolved _ _ = () in
''' + network[start:end] + '''
  {register;send;receive;receive_line;receive_frame;close;watch;listen_mailbox}
''')
PY
cp "$ROOT/test-suite/misc/soma_tcp_runtime.ml" check.ml
"${OCAMLC[@]}" -w -a -c uint63.ml soma_word64.ml soma_handles.ml float64.ml prog.mli prog.ml links.ml check.ml >> compile.log 2>&1
# macOS Bash 3 treats an empty array as unset under nounset.
"${OCAMLC[@]}" -o check ${LWT_FILES[@]+"${LWT_FILES[@]}"} uint63.cmo soma_word64.cmo soma_handles.cmo float64.cmo prog.cmo links.cmo check.cmo >> compile.log 2>&1
./check
