#!/usr/bin/env bash
# Device read errors must never become missing files or stale snapshots.
# Exercise the generated store verbatim, failing each sector read on reopen.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cd "$WORK"
sed -n '/^let source = {soma|/,$p' "$ROOT/toplevel/somaStorage.ml" | sed '1s/^let source = {soma|//; $d' > soma_store.ml
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
cat > check.ml <<'OCAML'
open Standins
module Block = struct
  type t = bytes array
  type error = [ `Disconnected ]
  type write_error = [ `Disconnected | `Is_read_only ]
  let reads = ref 0
  let fail_at = ref (-1)
  let writes = ref 0
  let get_info d = {Mirage_block.read_write=true; sector_size=512;
                    size_sectors=Int64.of_int (Array.length d)}
  let read d off buffers =
    let index = !reads in
    incr reads;
    if index = !fail_at then Error `Disconnected
    else begin
      List.iteri (fun i b -> Bytes.blit d.(Int64.to_int off+i) 0 b 0 512) buffers;
      Ok ()
    end
  let write d off buffers =
    incr writes;
    List.iteri (fun i b -> Bytes.blit b 0 d.(Int64.to_int off+i) 0 512) buffers;
    Ok ()
end
module Store = Soma_store.Make(Block)
let reopen disk failure =
  Block.reads := 0;
  Block.fail_at := failure;
  Store.connect disk
let expect_read_error f =
  match (try ignore (f ()); None with Failure s -> Some s) with
  | Some "Sandbox storage: device read failed" -> ()
  | _ -> failwith "device read error was hidden or misreported"
let check disk verify =
  let healthy = reopen disk (-1) in
  verify healthy;
  let count = !(Block.reads) in
  let before = Array.map Bytes.copy disk in
  let writes = !(Block.writes) in
  for index = 0 to count - 1 do
    expect_read_error (fun () -> reopen disk index);
    assert (!(Block.writes) = writes);
    assert (disk = before);
    (* A transient failure neither initializes nor repairs the disk. *)
    verify (reopen disk (-1))
  done;
  count
let () =
  let blank () = Array.init 128 (fun _ -> Bytes.make 512 '\000') in
  let n = check (blank ()) (fun store ->
    assert (Store.read store "missing" = None)) in
  let disk = blank () in
  let store = Store.connect disk in
  Store.write store "key" "old";
  Store.write store "key" (String.make 1800 'x');
  Store.write store "empty" "";
  Store.append store "key" "-tail";
  let n = n + check disk (fun store ->
    assert (Store.read store "key" = Some (String.make 1800 'x' ^ "-tail"));
    assert (Store.read store "empty" = Some "");
    assert (Store.read store "missing" = None)) in
  (* Even with a valid older bank, an unreadable newer bank is not an
     excuse to return stale contents as though recovery succeeded. *)
  Printf.printf "PASS %d sector read failures are explicit and leave disks unchanged\n" n
OCAML
ocamlc -c standins.ml
ocamlc -open Standins -c soma_store.ml check.ml
ocamlc -o check standins.cmo soma_store.cmo check.cmo
./check
