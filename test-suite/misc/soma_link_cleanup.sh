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
# the runtime's framing (Soma_rt.take_line, take_frame), as it is
framing = source[source.index('let max_frame ='):source.index('(* What the network provides')]
frames = source[source.index('type frame = '):source.index('\n', source.index('type frame = '))]
with open(sys.argv[2], 'w') as out:
    out.write('''module Lwt = struct
  type 'a t = 'a
  let return x = x
  let return_unit = ()
  let catch f h = try f () with e -> h e
  (* promises are values here: every one is already resolved *)
  let pick l = List.hd l
  let choose l = List.hd l
  (* a promise that never resolves: receive_frame's, which no case here
     reaches *)
  let wait () : 'a t * unit = (Obj.magic (), ())
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
module Ipaddr = struct let of_string s = Ok s let to_string s = s end
module Lwt_condition = struct
  let create () = ()
  let broadcast () () = ()
  let wait () = ()
end
module Soma_rt = struct
  type field = I of int | B of bool
  type mail = Mail_opened of int * string | Mail_bytes of int * string | Mail_closed of int
  type link = Link of int | Link_refused | Link_timed_out | Link_bad_address
  let event _ _ = ()
  let open_connections = ref 0
  let served = ref 0
  let report ~during:_ _ = ()
''' + frames + '\n' + framing + '''
end
module Duration = struct let of_sec s = s end
module Mirage_sleep = struct let ns _ = () end
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
    (* the handler listen was given: the test calls it with a flow *)
    let handler : (flow -> unit) option ref = ref None
    let listen _ ~port:_ h = handler := Some h
    let dst _ = ("192.0.2.7", 1234)
  end
  let tcp s = s
end
(* an open link, as Main's: its flow, what it received past the last line
   or frame taken, and the read under way *)
type link = { flow : S.TCP.flow; pending : Buffer.t; mutable reading : bool option }
let () =
    let s = () in
    let servers = ref 0 in
    let dial _ _ = `Refused in
    let dial_within _ _ _ = `Refused in
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
    (* the mailbox: a connection accepted, its two reads and its end, in
       order, and nothing after them *)
    listen_mailbox 9000;
    let f = flow ["one\ntw"; "o\n"] in
    (match !S.TCP.handler with Some h -> h f | None -> assert false);
    let got = mailbox (fun () -> ()) in
    (match got with
     | [Soma_rt.Mail_opened (a, "192.0.2.7"); Soma_rt.Mail_bytes (b, "one\ntw");
        Soma_rt.Mail_bytes (c, "o\n"); Soma_rt.Mail_closed d] ->
         assert (a = b && b = c && c = d)
     | _ -> assert false);
    assert (f.closed = 1);
    assert (mailbox (fun () -> ()) = []);
    ignore listen; ignore connect; ignore connect_within
''')
PY
ocamlc -w -a -o "$WORK/links" "$WORK/links.ml"
"$WORK/links"
