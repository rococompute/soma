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
  type t = bytes array
  type error = [ `Disconnected ]
  type write_error = [ `Disconnected | `Is_read_only ]
  let remaining = ref max_int and prefix = ref 0
  let get_info d = {Mirage_block.read_write=true; sector_size=512;
                    size_sectors=Int64.of_int (Array.length d)}
  let read d off bs = List.iteri (fun i b -> Bytes.blit d.(Int64.to_int off+i) 0 b 0 512) bs; Ok ()
  let write d off = function
    | [b] ->
      if !remaining = 0 then (Bytes.blit b 0 d.(Int64.to_int off) 0 !prefix; Error `Disconnected)
      else (decr remaining; Bytes.blit b 0 d.(Int64.to_int off) 0 512; Ok ())
    | _ -> assert false
end
module Store = Soma_store.Make(Block)
let blank () = Array.init 128 (fun _ -> Bytes.make 512 '\000')
let refused d = try ignore (Store.connect d); false with Failure _ -> true
let () =
  (* Pick a completed first commit with a nonzero final checksum byte.
     Zeroing just that byte used to look like a torn, uncommitted header. *)
  let rec seed n =
    assert (n < 256);
    let disk = blank () and text = "acknowledged-" ^ string_of_int n in
    Store.write (Store.connect disk) "key" text;
    if Bytes.get disk.(0) 55 = '\000' then seed (n+1) else disk,text
  in
  let disk,text = seed 0 in
  assert (Store.read (Store.connect disk) "key" = Some text);
  let damaged = Array.map Bytes.copy disk in
  Bytes.set damaged.(0) 55 '\000';
  if not (refused damaged) then failwith "checksum damage to acknowledged first commit mounted an empty store";
  print_endline "PASS acknowledged first checksum byte cannot become an empty disk";
  for i = 40 to 55 do
    let damaged = Array.map Bytes.copy disk in
    Bytes.set damaged.(0) i (Char.chr (Char.code (Bytes.get damaged.(0) i) lxor 1));
    let before = Array.map Bytes.copy damaged in
    assert (refused damaged);
    assert (damaged = before)
  done;
  print_endline "PASS all 16 first-header checksum corruptions refuse without writes";
  (* A receipt is a later write to the same, already complete header.
     A cut anywhere in it must retain that header's valid snapshot. *)
  for cut = 0 to 511 do
    let disk = blank () in
    let store = Store.connect disk in
    Block.remaining := 2; Block.prefix := cut;
    let failed = try Store.write store "key" "acknowledged"; false with Failure _ -> true in
    assert failed;
    Block.remaining := max_int;
    assert (Store.read store "key" = None);
    let recovered = Store.connect disk in
    assert (Store.read recovered "key" = Some "acknowledged");
    Store.append recovered "key" "-tail";
    assert (Store.read (Store.connect disk) "key" = Some "acknowledged-tail")
  done;
  print_endline "PASS all 512 interrupted first receipts retain a recoverable snapshot";
  (* Existing valid generation-1 images had zero padding. Keep them readable
     without claiming to distinguish later corruption from their first tear. *)
  let legacy = Array.map Bytes.copy disk in
  Bytes.fill legacy.(0) 56 (512-56) '\000';
  assert (Store.read (Store.connect legacy) "key" = Some text);
  print_endline "PASS valid legacy first headers remain readable"
OCAML
ocamlc -c standins.ml
ocamlc -open Standins -c soma_store.ml check.ml
ocamlc -o check standins.cmo soma_store.cmo check.cmo
./check

# The receipt must preserve recovery from an interrupted initial header and
# interrupted later snapshots, including every prefix of a torn sector.
for regression in soma_storage_torn_first.sh soma_storage_torn_sectors.sh soma_storage_interrupted.sh soma_storage_readonly.sh soma_storage_sector4096.sh; do
  bash "$ROOT/test-suite/misc/$regression"
done
