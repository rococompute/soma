#!/usr/bin/env bash
# Execute the boot-counting image example without a hypervisor. Each boot
# is a fresh process over the generated store and the same sector file.
# Check exact output and repeat on a fresh disk to rule out host state.
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE SOMA_MIRAGE_SWITCH
cd "$WORK"
cp "$ROOT/examples/example_files/mirage_storage/mirage_storage.soma" storage.soma
soma build --no-image storage.soma > build.log 2>&1
grep -q '(no image)' build.log
project="$SOMA_MIRAGE_DIR/plain-storage"
grep -q 'block_of_file "storage"' "$project/config.ml"
grep -Fq 'main "Unikernel.Main" (block @-> job)' "$project/config.ml"
cp "$project"/{prog.ml,prog.mli,uint63.ml,soma_word64.ml,float64.ml,soma_wasm.ml,soma_store.ml} .
# the program's signal and promise types, as checked (without Lwt)
cp "$project/no-image/soma_handles.ml" .
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
    transfer fd sector buffers true; Unix.fsync fd; Ok ()
end
module Store = Soma_store.Make(Block)
(* an image's strings are OCaml strings, its nats ints (the image's
   extraction: ExtrOcamlNativeString, ExtrOcamlNatInt) *)
let chars s = s
let text (s : string) = s
let nat (n : int) = n
let disk = Unix.openfile Sys.argv.(1) [Unix.O_RDWR] 0
let files = Store.connect disk
let rec run : 'a. 'a Prog.io -> 'a = fun m -> match m with
  | Prog.Ret x -> x
  | Prog.Bind (m,k) -> run (k (run m))
  | Prog.Print s -> print_endline (text s); Obj.magic ()
  | Prog.Exit n -> exit (nat n)
  | Prog.Read_file n -> Obj.magic (Option.map chars (Store.read files (text n)))
  | Prog.Write_file (n,d) -> Store.write files (text n) (text d); Obj.magic ()
  | Prog.Append_file (n,d) -> Store.append files (text n) (text d); Obj.magic ()
  | _ -> failwith "unexpected nonstorage operation"
let () = run (Prog.soma_main ()); Unix.close disk
OCAML
ocamlc -c standins.ml
ocamlc -open Standins -c uint63.ml soma_word64.ml soma_handles.ml float64.ml soma_wasm.ml prog.mli prog.ml soma_store.ml driver.ml
ocamlc -o storage-run unix.cma standins.cmo uint63.cmo soma_word64.cmo soma_handles.cmo float64.cmo soma_wasm.cmo prog.cmo soma_store.cmo driver.cmo
truncate -s 65536 disk.img
for boot in 1 2 3; do
  ./storage-run disk.img > "boot-$boot.log"
  printf 'storage checks passed\nboot %s\n' "$boot" > expected.log
  diff -u expected.log "boot-$boot.log"
done
truncate -s 65536 fresh.img
./storage-run fresh.img > fresh.log
printf 'storage checks passed\nboot 1\n' > expected.log
diff -u expected.log fresh.log
echo 'PASS extracted image example: three persistent boots and a fresh disk'
