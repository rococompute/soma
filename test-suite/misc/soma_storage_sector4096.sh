#!/usr/bin/env bash
# The generated store on a 4096-byte-sector device (Solo5/Mirage block
# devices are not always 512): basic operations across reopens, a value
# spanning several payload sectors, the exact capacity boundary, and
# recovery when the second bank's header is corrupt. Uses the generated
# backend verbatim; no image tools needed.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cd "$WORK"
python3 - "$ROOT/toplevel/somaStorage.ml" > soma_store.ml <<'PYEOF'
import sys
t = open(sys.argv[1]).read()
sys.stdout.write(t.split("{soma|", 1)[1].split("|soma}", 1)[0])
PYEOF
grep -q 'module Make' soma_store.ml
cat > standins.ml <<'OCAML'
module Lwt = struct
  type 'a t = 'a
  let return x = x
  let return_unit = ()
  module Infix = struct let ( >>= ) x f = f x let ( >|= ) x f = f x end
end
module Lwt_mutex = struct
  type t = unit
  let create () = ()
  let with_lock () f = f ()
end
module Cstruct = struct
  type t = bytes
  let create = Bytes.create
  let of_string = Bytes.of_string
  let to_string = Bytes.to_string
end
module Mirage_block = struct
  type info = {read_write:bool; sector_size:int; size_sectors:int64}
  module type S = sig
    type t
    type error = private [> `Disconnected ]
    type write_error = private [> `Disconnected | `Is_read_only ]
    val get_info : t -> info Lwt.t
    val read : t -> int64 -> Cstruct.t list -> (unit,error) result Lwt.t
    val write : t -> int64 -> Cstruct.t list -> (unit,write_error) result Lwt.t
  end
end
OCAML
cat > driver.ml <<'OCAML'
open Standins
module Block = struct
  type t = bytes array
  type error = [ `Disconnected ]
  type write_error = [ `Disconnected | `Is_read_only ]
  let get_info d = {Mirage_block.read_write=true; sector_size=4096;
                    size_sectors=Int64.of_int (Array.length d)}
  let read d off buffers =
    List.iteri (fun i b -> Bytes.blit d.(Int64.to_int off+i) 0 b 0 4096) buffers;
    Ok ()
  let write d off buffers =
    List.iteri (fun i b -> Bytes.blit b 0 d.(Int64.to_int off+i) 0 4096) buffers;
    Ok ()
end
module Store = Soma_store.Make(Block)
let check label ok = if ok then Printf.printf "ok %s\n%!" label else (Printf.printf "FAIL %s\n%!" label; exit 1)
let () =
  (* 32 sectors of 4096: two banks of 16 sectors, payload capacity
     (16-1)*4096 = 61440 bytes per bank *)
  let disk = Array.init 32 (fun _ -> Bytes.make 4096 '\000') in
  let s = Store.connect disk in
  check "missing on blank 4096 disk" (Store.read s "key" = None);
  Store.write s "key" "old";
  check "write then reopen" (Store.read (Store.connect disk) "key" = Some "old");
  Store.write s "key" "secret";
  Store.write s "log" "one"; Store.append s "log" "-two"; Store.append s "log" "-three";
  Store.write s "empty" "before"; Store.write s "empty" "";
  let r = Store.connect disk in
  check "overwrite, appends in order, independent names, empty not missing"
    (Store.read r "key" = Some "secret" && Store.read r "log" = Some "one-two-three"
     && Store.read r "empty" = Some "" && Store.read r "missing" = None);
  let big = String.make 20000 'z' in
  Store.write r "big" big;
  check "value spanning payload sectors at 4096" (Store.read (Store.connect disk) "big" = Some big);
  (* one file "k": encoded payload is 4 + (4+1+4+len); exactly 61440 fits *)
  let disk2 = Array.init 32 (fun _ -> Bytes.make 4096 '\000') in
  let s2 = Store.connect disk2 in
  Store.write s2 "k" (String.make 61427 'a');
  check "payload at exact capacity commits"
    (Store.read (Store.connect disk2) "k" = Some (String.make 61427 'a'));
  (try Store.write s2 "k" (String.make 61428 'b'); check "one byte past capacity refused" false
   with Failure msg -> check "one byte past capacity refused" (msg = "Sandbox storage: disk full"));
  check "refused write preserves committed value at 4096"
    (Store.read (Store.connect disk2) "k" = Some (String.make 61427 'a'));
  (* corrupt the second bank's header (sector 16): fall back, then repair *)
  Store.write s "key" "newest";
  Bytes.set disk.(16) 0 '\255';
  let recd = Store.connect disk in
  check "corrupt second-bank header recovers older value" (Store.read recd "key" = Some "secret");
  Store.write recd "key" "repaired";
  check "write after second-bank recovery reopens" (Store.read (Store.connect disk) "key" = Some "repaired");
  print_endline "PASS 4096-byte sectors, capacity boundary, second-bank recovery"
OCAML
ocamlc -c standins.ml
ocamlc -open Standins -c soma_store.ml driver.ml
ocamlc -o run standins.cmo soma_store.cmo driver.cmo
./run > out.log 2>&1 || { cat out.log; exit 1; }
cat out.log
! grep -q '^FAIL ' out.log
[ "$(grep -c '^ok ' out.log)" -eq 9 ]
grep -qx 'PASS 4096-byte sectors, capacity boundary, second-bank recovery' out.log
