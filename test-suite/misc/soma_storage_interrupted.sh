#!/usr/bin/env bash
# An interrupted multi-sector commit must not poison recovery: after a
# write that dies mid-payload, a fresh connect still reads the last
# committed value, a shorter successful write then commits, and another
# reopen reads it. Exercises the generated store (toplevel/somaStorage.ml)
# directly over a sector file; no image tools needed.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cd "$WORK"
# the generated Mirage store source, verbatim between its markers
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
  type t = Unix.file_descr
  type error = [ `Disconnected ]
  type write_error = [ `Disconnected | `Is_read_only ]
  let calls = ref 0 and fail_at = ref (-1)
  let get_info _ = {Mirage_block.read_write=true; sector_size=512; size_sectors=128L}
  let transfer fd sector buffers write =
    ignore (Unix.LargeFile.lseek fd (Int64.mul sector 512L) Unix.SEEK_SET);
    List.iter (fun b ->
      assert (Bytes.length b = 512);
      let rec loop pos = if pos < 512 then
        let n = (if write then Unix.write else Unix.read) fd b pos (512-pos) in
        if n = 0 then failwith "short disk transfer" else loop (pos+n)
      in loop 0) buffers
  let read fd sector buffers = transfer fd sector buffers false; Ok ()
  let write fd sector buffers =
    incr calls;
    if !fail_at = !calls then Error `Disconnected
    else (transfer fd sector buffers true; Unix.fsync fd; Ok ())
end
module Store = Soma_store.Make(Block)
let check label ok = if ok then Printf.printf "ok %s\n%!" label else (Printf.printf "FAIL %s\n%!" label; exit 1)
let () =
  let disk = Unix.openfile Sys.argv.(1) [Unix.O_RDWR] 0 in
  let long1 = String.make 5000 'a' in
  let long2 = String.make 9000 'b' in
  let s = Store.connect disk in
  check "missing before any write" (Store.read s "key" = None);
  Store.write s "key" long1;
  check "long value committed" (Store.read (Store.connect disk) "key" = Some long1);
  (* die on the third sector write of the next commit: payload is cut
     mid-way, its header never lands *)
  Block.fail_at := !Block.calls + 3;
  (try Store.write s "key" long2; check "interrupted write refused" false
   with Failure _ -> check "interrupted write refused" true);
  Block.fail_at := -1;
  let r = Store.connect disk in
  check "recovery reads last committed, not the cut payload" (Store.read r "key" = Some long1);
  Store.write r "key" "short";
  let r2 = Store.connect disk in
  check "shorter write after interruption commits" (Store.read r2 "key" = Some "short");
  Store.append r2 "key" "-tail";
  check "append after recovery, reopened" (Store.read (Store.connect disk) "key" = Some "short-tail");
  check "missing still missing" (Store.read (Store.connect disk) "nope" = None);
  Unix.close disk;
  print_endline "PASS interrupted commit recovery"
OCAML
ocamlc -c standins.ml
ocamlc -open Standins -c soma_store.ml driver.ml
ocamlc -o run unix.cma standins.cmo soma_store.cmo driver.cmo
truncate -s 65536 disk.img
./run disk.img > out.log 2>&1 || { cat out.log; exit 1; }
cat out.log
! grep -q '^FAIL ' out.log
[ "$(grep -c '^ok ' out.log)" -eq 7 ]
grep -qx 'PASS interrupted commit recovery' out.log
