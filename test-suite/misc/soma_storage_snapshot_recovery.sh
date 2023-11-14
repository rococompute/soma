#!/usr/bin/env bash
# Exercise every interrupted sector write of a multi-sector snapshot, then
# retry with a shorter payload and reopen again. Uses the generated backend.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cd "$WORK"
# Extract the exact source used in images, without needing the Soma compiler.
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
  let remaining = ref max_int
  let get_info d = {Mirage_block.read_write=true; sector_size=512;
                    size_sectors=Int64.of_int (Array.length d)}
  let read d off buffers =
    List.iteri (fun i b -> Bytes.blit d.(Int64.to_int off+i) 0 b 0 512) buffers;
    Ok ()
  let write d off buffers =
    if !remaining = 0 then Error `Disconnected else begin
      decr remaining;
      List.iteri (fun i b -> Bytes.blit b 0 d.(Int64.to_int off+i) 0 512) buffers;
      Ok ()
    end
end
module Store = Soma_store.Make(Block)
let copy = Array.map Bytes.copy
let expect t name value = assert (Store.read t name = value)
let () =
  let original = Array.init 128 (fun _ -> Bytes.make 512 '\000') in
  let initial = Store.connect original in
  Store.write initial "key" "committed";
  Store.write initial "other" "independent";
  (* The replacement occupies four payload sectors plus its header. Each
     failure leaves the previous committed bank recoverable. *)
  for completed = 0 to 4 do
    let disk = copy original in
    let store = Store.connect disk in
    Block.remaining := completed;
    let failed = try Store.write store "key" (String.make 1800 'x'); false
                 with Failure _ -> true in
    assert failed;
    Block.remaining := max_int;
    let recovered = Store.connect disk in
    expect recovered "key" (Some "committed");
    expect recovered "other" (Some "independent");
    Store.write recovered "key" "short";
    let reopened = Store.connect disk in
    expect reopened "key" (Some "short");
    expect reopened "other" (Some "independent");
    Store.append reopened "key" "-tail";
    expect (Store.connect disk) "key" (Some "short-tail")
  done;
  (* On a blank disk, uncommitted payload has no header. A shorter first
     commit must not interpret abandoned sectors as later records. *)
  for completed = 0 to 4 do
    let disk = Array.init 128 (fun _ -> Bytes.make 512 '\000') in
    let store = Store.connect disk in
    Block.remaining := completed;
    let failed = try Store.write store "key" (String.make 1800 'x'); false
                 with Failure _ -> true in
    assert failed;
    Block.remaining := max_int;
    let recovered = Store.connect disk in
    expect recovered "key" None;
    Store.write recovered "key" "short";
    expect (Store.connect disk) "key" (Some "short")
  done;
  (* Corrupt either the newest header or payload, recover the older bank,
     and prove the damaged bank can be replaced by a new commit. *)
  List.iter (fun sector ->
    let disk = copy original in
    Store.write (Store.connect disk) "key" "newest";
    Bytes.set disk.(sector) 0 '\255';
    let recovered = Store.connect disk in
    expect recovered "key" (Some "committed");
    expect recovered "other" (Some "independent");
    Store.write recovered "key" "repaired";
    expect (Store.connect disk) "key" (Some "repaired")
  ) [0; 1];
  print_endline "PASS interrupted multi-sector snapshots, shorter retries, and corrupt-bank recovery"
OCAML
ocamlc -c standins.ml
ocamlc -open Standins -c soma_store.ml check.ml
ocamlc -o check standins.cmo soma_store.cmo check.cmo
./check
