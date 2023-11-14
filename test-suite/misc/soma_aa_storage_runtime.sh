#!/usr/bin/env bash
# Execute the extracted Soma storage program against the generated block
# backend. The synchronous Lwt stand-in and sector-file adapter require no
# image tools; fresh processes reopen the same disk, never an in-memory map.
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE SOMA_MIRAGE_SWITCH
cd "$WORK"
cat > storage.soma <<'SOMA'
Require Import Sandbox.
Definition expect (name : string) (want : option string) : io unit :=
  got <- read_file name ;;
  if match got, want with
     | None, None => true
     | Some a, Some b => String.eqb a b
     | _, _ => false end
  then print (String.append "ok " name)
  else (print (String.append "FAIL " name) ;; exit 1).
Definition main : io unit :=
  mode <- args ;;
  match mode with
  | cons "verify" _ =>
      expect "key" (Some "secret") ;;
      expect "log" (Some "one-two-three") ;;
      expect "empty" (Some "") ;;
      expect "../key" (Some "opaque") ;;
      expect "missing" None ;;
      expect "created" (Some "tail") ;;
      expect "binary" (Some ("a" ++ byte 0 ++ newline)%str)
  | _ =>
      expect "missing" None ;;
      write_file "key" "old" ;; expect "key" (Some "old") ;;
      write_file "key" "secret" ;; expect "key" (Some "secret") ;;
      write_file "log" "one" ;; append_file "log" "-two" ;; append_file "log" "-three" ;;
      expect "log" (Some "one-two-three") ;;
      write_file "empty" "before" ;; write_file "empty" "" ;; expect "empty" (Some "") ;;
      append_file "created" "tail" ;; expect "created" (Some "tail") ;;
      write_file "../key" "opaque" ;; expect "../key" (Some "opaque") ;; expect "key" (Some "secret") ;;
      write_file "binary" ("a" ++ byte 0 ++ newline)%str ;; expect "binary" (Some ("a" ++ byte 0 ++ newline)%str)
  end.
SOMA
soma build --no-image storage.soma > build.log 2>&1
grep -q '(no image)' build.log
project="$SOMA_MIRAGE_DIR/plain-storage"
grep -q 'block_of_file "storage"' "$project/config.ml"
grep -Fq 'main "Unikernel.Main" (block @-> job)' "$project/config.ml"
cp "$project"/{prog.ml,prog.mli,float64.ml,soma_wasm.ml,soma_store.ml} .
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
  let calls = ref 0 and fail_at = ref 0
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
let chars s = List.of_seq (String.to_seq s)
let text s = String.of_seq (List.to_seq (Obj.magic s : char list))
let nat n = let rec go a = function Prog.O -> a | Prog.S n -> go (a+1) n in go 0 n
let disk = Unix.openfile Sys.argv.(1) [Unix.O_RDWR] 0
let files = Store.connect disk
let rec run : 'a. 'a Prog.io -> 'a = fun m -> match m with
  | Prog.Ret x -> x
  | Prog.Bind (m,k) -> run (k (run m))
  | Prog.Print s -> print_endline (text s); Obj.magic ()
  | Prog.Args -> Obj.magic (if Sys.argv.(2) = "verify" then [chars "verify"] else [])
  | Prog.Exit n -> exit (nat n)
  | Prog.Read_file n -> Obj.magic (Option.map chars (Store.read files (text n)))
  | Prog.Write_file (n,d) -> Store.write files (text n) (text d); Obj.magic ()
  | Prog.Append_file (n,d) -> Store.append files (text n) (text d); Obj.magic ()
  | _ -> failwith "unexpected nonstorage operation"
let () =
  if Sys.argv.(2) = "faults" then begin
    let check_failure f = try f (); failwith "accepted failed write" with Failure s ->
      if s = "accepted failed write" then failwith s in
    Block.calls := 0; Block.fail_at := 2;
    check_failure (fun () -> Store.write files "key" "lost");
    Block.fail_at := 0;
    let recovered = Store.connect disk in
    assert (Store.read recovered "key" = Some "secret");
    check_failure (fun () -> Store.write recovered "full" (String.make 65536 'x'));
    assert (Store.read recovered "full" = None);
    assert (Store.read (Store.connect disk) "key" = Some "secret");
    print_endline "ok failed commit and disk full preserve committed state"
  end else run (Prog.soma_main ());
  Unix.close disk
OCAML
ocamlc -c standins.ml
ocamlc -open Standins -c float64.ml soma_wasm.ml prog.mli prog.ml soma_store.ml driver.ml
ocamlc -o storage-run unix.cma standins.cmo float64.cmo soma_wasm.cmo prog.cmo soma_store.cmo driver.cmo
truncate -s 65536 disk.img
./storage-run disk.img first > first.log
./storage-run disk.img verify > verify.log
./storage-run disk.img faults > faults.log
! grep -q '^FAIL ' first.log verify.log
[ "$(grep -c '^ok ' first.log)" -eq 9 ]
[ "$(grep -c '^ok ' verify.log)" -eq 7 ]
grep -q '^ok failed commit' faults.log
cat first.log verify.log faults.log
# Read-only access through a variable still requests the block device.
cat > read_only.soma <<'SOMA'
Require Import Sandbox.
Definition main : io unit :=
  names <- args ;;
  match names with
  | cons name _ => value <- read_file name ;; print (match value with Some s => s | None => "missing" end)
  | nil => ret tt end.
SOMA
SOMA_MIRAGE_DIR="$WORK/read-only" soma build --no-image read_only.soma > read-only.log 2>&1
test -f "$WORK/read-only/plain-storage/no-image/unikernel.cmo"
# Both functor arguments must type-check when a program uses TCP and files.
cat > network_storage.soma <<'SOMA'
Require Import Sandbox.
Definition main : io unit := listen 9000 (fun _ => write_file "key" "value").
SOMA
SOMA_MIRAGE_DIR="$WORK/network" soma build --no-image network_storage.soma > network.log 2>&1
test -f "$WORK/network/net-storage/no-image/unikernel.cmo"
# Non-storage images still type-check against their original interfaces.
cd "$ROOT"
bash test-suite/misc/soma_no_image.sh > "$WORK/old-no-image.log" 2>&1
sh dev/mirage-check.sh --no-image > "$WORK/all-no-image.log" 2>&1
if opam switch list --short 2>/dev/null | grep -qx hvf; then
  sh dev/mirage-check.sh --storage-only > "$WORK/image.log" 2>&1
else
  echo 'SKIP image boots: no hvf Mirage switch; sector-file reopen and no-image checks ran'
fi
echo 'PASS actual named-file operations, disk reopen, failed commit and all no-image examples'
