#!/usr/bin/env bash
# The first commit on a blank disk, cut short at every byte of its header
# sector, must leave a disk that opens (empty, or with the commit once its
# checksummed header is whole) and takes the next commit; a header that is
# not a cut-short first header is still refused. Runs the exact generated
# storage backend.
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
let blank () = Array.init 128 (fun _ -> Bytes.make 512 '\000')
let expect t name value = assert (Store.read t name = value)
let refused disk = try ignore (Store.connect disk); false with Failure _ -> true
let () =
  (* "committed" is one payload sector; the header is the second write *)
  for torn = 0 to 511 do
    let disk = blank () in
    let store = Store.connect disk in
    Block.remaining := 1;
    Block.prefix := torn;
    let failed = try Store.write store "key" "committed"; false
      with Failure _ -> true in
    assert failed;
    Block.remaining := max_int;
    expect store "key" None;
    let recovered = Store.connect disk in
    let expected = if torn >= 56 then Some "committed" else None in
    expect recovered "key" expected;
    expect recovered "missing" None;
    Store.write recovered "key" "short";
    Store.append recovered "key" "-tail";
    let reopened = Store.connect disk in
    expect reopened "key" (Some "short-tail");
    Store.write reopened "other" "independent";
    let again = Store.connect disk in
    expect again "key" (Some "short-tail");
    expect again "other" (Some "independent")
  done;
  (* a whole first header with a damaged generation is not cut short *)
  let disk = blank () in
  Store.write (Store.connect disk) "key" "committed";
  Bytes.set disk.(0) 8 '\255';
  assert (refused disk);
  (* nor is a sector that never held a Soma header *)
  let disk = blank () in
  Bytes.blit_string "not a soma disk" 0 disk.(0) 0 15;
  assert (refused disk);
  (* nor is anything past the header's checksum *)
  let disk = blank () in
  Bytes.blit_string "SOMAKV01" 0 disk.(0) 0 8;
  Bytes.set disk.(0) 100 'x';
  assert (refused disk);
  (* a cut-short header in the second bank, with an empty first, is refused:
     commits never start there *)
  let disk = blank () in
  Bytes.blit_string "SOMAKV01" 0 disk.(64) 0 8;
  assert (refused disk);
  print_endline "PASS 512 cut-short first headers recover; foreign and damaged headers refused"
OCAML
ocamlc -c standins.ml
ocamlc -open Standins -c soma_store.ml check.ml
ocamlc -o check standins.cmo soma_store.cmo check.cmo
./check
