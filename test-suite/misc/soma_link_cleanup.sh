#!/usr/bin/env bash
# Exercise the generated link implementation with deterministic TCP reads.
# No switch, network, timers, or concurrent processes are needed.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
python3 - "$ROOT/toplevel/somaMirage.ml" "$WORK/links.ml" <<'PY'
import sys
source = open(sys.argv[1]).read()
start = source.index('    let links = Hashtbl.create 7')
end = source.index('    Soma_rt.main ~network:true', start)
with open(sys.argv[2], 'w') as out:
    out.write('''module Lwt = struct
  let return x = x
  let return_unit = ()
  let catch f h = try f () with e -> h e
  module Infix = struct
    let ( >>= ) x f = f x
    let ( >|= ) x f = f x
  end
end
open Lwt.Infix
module Cstruct = struct
  let of_string x = x
  let to_string x = x
end
module Ipaddr = struct let of_string s = Ok s end
module Soma_rt = struct
  type field = I of int
  type link = Link of int | Link_refused | Link_timed_out | Link_bad_address
  let event _ _ = ()
  let open_connections = ref 0
  let served = ref 0
  let report ~during:_ _ = ()
end
module S = struct
  module TCP = struct
    type flow = { mutable reads : string list; mutable closed : int;
                  mutable writes_fail : bool; mutable read_count : int }
    let close f = f.closed <- f.closed + 1
    let read f =
      f.read_count <- f.read_count + 1;
      match f.reads with
      | [] -> Ok `Eof
      | s :: rest -> f.reads <- rest; Ok (`Data s)
    let write f _ = if f.writes_fail then Error `Closed else Ok ()
    let listen _ ~port:_ _ = ()
  end
  let tcp s = s
end
let () =
    let s = () in
    let servers = ref 0 in
    let dial _ _ = `Refused in
''')
    out.write(source[start:end])
    out.write('''    let flow reads = S.TCP.{ reads; closed = 0; writes_fail = false; read_count = 0 } in
    let f = flow ["first\\r"; "\\nsecond\\npartial"] in
    let id = register f in
    assert (receive_line id = Some "first");
    assert (receive_line id = Some "second");
    assert (f.read_count = 2);
    assert (receive_line id = None);
    assert (f.closed = 1);
    assert (not (Hashtbl.mem links id));
    assert (receive_line id = None);
    assert (not (send id "after EOF"));
    close id;
    assert (f.closed = 1);
    let f = flow [] in
    let id = register f in
    assert (send id "hello");
    f.writes_fail <- true;
    assert (not (send id "failed"));
    assert (f.closed = 1);
    assert (not (Hashtbl.mem links id));
    close id;
    assert (f.closed = 1);
    ignore listen; ignore connect
''')
PY
ocamlc -w -a -o "$WORK/links" "$WORK/links.ml"
"$WORK/links"
