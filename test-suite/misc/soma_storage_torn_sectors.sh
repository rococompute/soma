#!/usr/bin/env bash
# Tear each payload/header sector at every byte boundary while replacing
# an already committed snapshot. Run the exact generated storage backend.
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
  let prefix = ref 0
  let get_info d = {Mirage_block.read_write=true; sector_size=512;
                    size_sectors=Int64.of_int (Array.length d)}
  let read d off buffers =
    List.iteri (fun i b -> Bytes.blit d.(Int64.to_int off+i) 0 b 0 512) buffers;
    Ok ()
  let write d off = function
    | [b] ->
      let target = d.(Int64.to_int off) in
      if !remaining = 0 then begin
        Bytes.blit b 0 target 0 !prefix;
        Error `Disconnected
      end else begin
        decr remaining;
        Bytes.blit b 0 target 0 512;
        Ok ()
      end
    | _ -> assert false
end
module Store = Soma_store.Make(Block)
let expect t name value = assert (Store.read t name = value)
let () =
  let original = Array.init 128 (fun _ -> Bytes.make 512 '\000') in
  let initial = Store.connect original in
  Store.write initial "key" "committed";
  Store.write initial "other" "independent";
  (* Exercise both target banks with different previous generations.
     Every replacement uses four payload sectors and one final header. *)
  List.iter (fun reused ->
    let baseline = Array.map Bytes.copy original in
    if reused then Store.write (Store.connect baseline) "key" "committed";
    for completed = 0 to 4 do
      for torn = 0 to 511 do
        let disk = Array.map Bytes.copy baseline in
        let store = Store.connect disk in
        Block.remaining := completed;
        Block.prefix := torn;
        let failed = try
          Store.write store "key" (String.make 1800 'x'); false
          with Failure _ -> true in
        assert failed;
        Block.remaining := max_int;
        (* Failed commits must not publish tentative in-memory contents. *)
        expect store "key" (Some "committed");
        let recovered = Store.connect disk in
        (* Once the whole checksummed header has reached disk, its zero
           padding may tear without invalidating the successful commit. *)
        let expected = if completed = 4 && torn >= 56
          then String.make 1800 'x' else "committed" in
        expect recovered "key" (Some expected);
        expect recovered "other" (Some "independent");
        expect recovered "missing" None;
        Store.write recovered "key" "short";
        Store.append recovered "key" "-tail";
        let reopened = Store.connect disk in
        expect reopened "key" (Some "short-tail");
        expect reopened "other" (Some "independent")
      done
    done
  ) [false; true];
  print_endline "PASS 5120 torn-sector commits and shorter retries"
OCAML
ocamlc -c standins.ml
ocamlc -open Standins -c soma_store.ml check.ml
ocamlc -o check standins.cmo soma_store.cmo check.cmo
./check
