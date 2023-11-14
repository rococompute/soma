#!/usr/bin/env bash
# Exercise the generated store verbatim on a read-only block device.
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
  type t = { sectors : bytes array; writable : bool }
  type error = [ `Disconnected ]
  type write_error = [ `Disconnected | `Is_read_only ]
  let writes = ref 0
  let get_info d = {Mirage_block.read_write=d.writable; sector_size=512;
                    size_sectors=Int64.of_int (Array.length d.sectors)}
  let read d off buffers =
    List.iteri (fun i b -> Bytes.blit d.sectors.(Int64.to_int off+i) 0 b 0 512) buffers;
    Ok ()
  let write d off buffers =
    incr writes;
    if not d.writable then Error `Is_read_only
    else begin
      List.iteri (fun i b -> Bytes.blit b 0 d.sectors.(Int64.to_int off+i) 0 512) buffers;
      Ok ()
    end
end
module Store = Soma_store.Make(Block)
let rejected f =
  match (try f (); None with Failure s -> Some s) with
  | Some "Sandbox storage: device is read-only" -> ()
  | _ -> failwith "expected explicit read-only failure"
let () =
  let disk = {Block.sectors=Array.init 128 (fun _ -> Bytes.make 512 '\000'); writable=true} in
  let store = Store.connect disk in
  Store.write store "key" "persisted";
  Store.write store "empty" "";
  let before = Array.map Bytes.copy disk.Block.sectors in
  let count = !(Block.writes) in
  let ro = Store.connect {disk with Block.writable=false} in
  assert (Store.read ro "key" = Some "persisted");
  assert (Store.read ro "empty" = Some "");
  assert (Store.read ro "missing" = None);
  rejected (fun () -> Store.write ro "key" "replacement");
  rejected (fun () -> Store.append ro "key" "-tail");
  rejected (fun () -> Store.append ro "missing" "new");
  rejected (fun () -> Store.write ro "empty" "");
  assert (!(Block.writes) = count);
  assert (disk.Block.sectors = before);
  assert (Store.read ro "key" = Some "persisted");
  assert (Store.read ro "missing" = None);
  let reopened = Store.connect disk in
  assert (Store.read reopened "key" = Some "persisted");
  Store.append reopened "key" "-tail";
  assert (Store.read (Store.connect disk) "key" = Some "persisted-tail");
  let blank = {Block.sectors=Array.init 128 (fun _ -> Bytes.make 512 '\000'); writable=false} in
  let empty = Store.connect blank in
  assert (Store.read empty "missing" = None);
  let count = !(Block.writes) in
  rejected (fun () -> Store.write empty "missing" "new");
  assert (!(Block.writes) = count);
  print_endline "PASS read-only disks retain reads and reject mutations before device writes"
OCAML
ocamlc -c standins.ml
ocamlc -open Standins -c soma_store.ml check.ml
ocamlc -o check standins.cmo soma_store.cmo check.cmo
./check
