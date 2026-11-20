#!/usr/bin/env bash
# Sandbox buffers, signals, free_cell and forget, checked without an
# image: a buffer is bytes, a signal and a promise soma_handles.ml's
# types, and the disks a program reads into buffers are its disks. A
# definition can name buffer without making its program an image; C takes
# a buffer as an argument and never gives one. With ocamlfind and lwt on
# PATH, an image's OCaml promise and C buffer are checked too.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 30 "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
export SOMA_MIRAGE_SWITCH=nonexistent
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cd "$WORK"

# the example: its disk is named by disk_read_into and disk_write_from too
cp "$ROOT/examples/example_files/mirage_buffers/mirage_buffers.soma" .
soma build --no-image mirage_buffers.soma > buffers.log 2>&1
grep -q 'mirage/plain-disk-data (no image)' buffers.log
P="$SOMA_MIRAGE_DIR/plain-disk-data"
grep -q 'Bytes.t' "$P/prog.mli"
grep -q 'Soma_handles.signal' "$P/prog.mli"
grep -q 'Soma_handles.promise' "$P/prog.mli"
grep -q '^type signal$' "$P/no-image/soma_handles.ml"
grep -q "^type 'a promise = 'a Lwt.t$" "$P/soma_handles.ml"

# Exercise the emitted buffer bounds and block adapter with a huge fake
# disk: count * sector_size must not wrap into a small accepted transfer.
mkdir runtime
cp "$P/soma_disk.ml" runtime/
sed -n '/^type disk = {/,/^(\* a signal/p' "$P/soma_rt.ml" | sed '$d' > runtime/soma_rt.ml
cat > runtime/standins.ml <<'OCAML'
module Lwt = struct
  type 'a t = 'a
  let return x = x
  module Infix = struct
    let ( >>= ) x f = f x
    let ( >|= ) x f = f x
  end
end
module Cstruct = struct
  type t = bytes
  let create = Bytes.create
  let to_string = Bytes.to_string
  let of_string = Bytes.of_string
  let blit_to_bytes = Bytes.blit
  let blit_from_bytes = Bytes.blit
end
module Mirage_block = struct
  type info = { sector_size : int; size_sectors : int64; read_write : bool }
  module type S = sig
    type t
    val get_info : t -> info Lwt.t
    val read : t -> int64 -> Cstruct.t list -> (unit, unit) result Lwt.t
    val write : t -> int64 -> Cstruct.t list -> (unit, unit) result Lwt.t
  end
end
OCAML
cat > runtime/check.ml <<'OCAML'
open Standins
let reads = ref 0
let writes = ref 0
module Block = struct
  type t = bool
  let get_info read_write = { Mirage_block.sector_size = 512;
    size_sectors = Int64.max_int; read_write }
  let read _ _ buffers = incr reads; List.iter (fun b -> Bytes.fill b 0 (Bytes.length b) 'x') buffers; Ok ()
  let write _ _ _ = incr writes; Ok ()
end
module Disk = Soma_disk.Make(Block)
let () =
  let b = Bytes.make 1024 'a' in
  assert (not (Soma_rt.in_buffer b max_int 1));
  assert (not (Soma_rt.in_buffer b 1 max_int));
  let d = Disk.make true in
  assert (not (d.read_into 0 (1 lsl (Sys.int_size - 9)) b 0));
  assert (not (d.read_into 0 1 b max_int));
  assert (not (d.read_into 0 3 b 0));
  assert (!reads = 0 && Bytes.get b 0 = 'a');
  assert (d.read_into 0 1 b 512 && !reads = 1 && Bytes.get b 512 = 'x');
  assert (d.read_into 0 0 b 1024 && !reads = 1);
  assert (not (d.write_from 0 b max_int 512));
  assert (not ((Disk.make false).write_from 0 b 0 512));
  assert (!writes = 0);
  assert (d.write_from 0 b 0 512 && !writes = 1)
OCAML
(cd runtime && ocamlc -c standins.ml &&
 ocamlc -open Standins -c soma_rt.ml soma_disk.ml check.ml &&
 ocamlc -o check standins.cmo soma_rt.cmo soma_disk.cmo check.cmo && ./check)

# a disk named only by disk_read_into is declared
cat > into.soma <<'SOMA'
Require Import Sandbox.
main : io unit := b <- new_buffer 512 ;; ok <- disk_read_into "raw" 0 1 b 0 ;; ret tt.
SOMA
soma build --no-image into.soma > into.log 2>&1
grep -q 'mirage/plain-disk-raw (no image)' into.log

# a definition that names buffer and promise, in an executable: still an
# executable, since naming them does not require Sandbox
mkdir exe
printf '[project]\nname = "exe"\nversion = "0.1.0"\n' > exe/soma.toml
printf 'make : nat -> buffer.\nlen : buffer -> nat.\n' > exe/sizes.definition
printf 'let make n = Bytes.make n '\''x'\''\nlet len = Bytes.length\n' > exe/sizes.ml
printf 'Import sizes.\nmain : string := to_string (len (make 7)).\n' > exe/main.soma
(cd exe && SOMA_MIRAGE_DIR="$WORK/exe-mirage" soma build main.soma > ../exe.log 2>&1)
[ "$(exe/main.exe)" = "7" ]
if [ -e "$WORK/exe-mirage" ] || grep -q Mirage exe.log; then
    echo 'a definition naming buffer made its program an image' >&2; exit 1
fi

# C never gives a buffer
mkdir cbuf
cp exe/soma.toml cbuf/
printf 'make : nat -> buffer.\n' > cbuf/bad.definition
printf '#include "bad.soma.h"\n' > cbuf/bad.c
cat > cbuf/main.soma <<'SOMA'
Require Import Sandbox.
Import bad.
main : io unit := b <- call (fun _ => make 4) ;; ret tt.
SOMA
if (cd cbuf && soma build --no-image main.soma > ../cbuf.log 2>&1); then
    echo 'a C function giving a buffer was accepted' >&2; exit 1
fi
grep -q 'C has no buffer result' cbuf.log

# an image's OCaml promise (later.ml) and C buffer (pattern.c), which
# needs lwt, by ocamlfind
if command -v ocamlfind >/dev/null && ocamlfind query lwt >/dev/null 2>&1; then
    cp -R "$ROOT/examples/example_projects/native_handles" handles
    rm -rf handles/.soma-cache
    (cd handles && soma build --no-image main.soma > ../handles.log 2>&1)
    grep -q '(no image)' handles.log
    grep -rq 'Soma_handles.promise' "$SOMA_MIRAGE_DIR"/*/soma_bindings.ml
    grep -rq 'soma_bytes a0' "$SOMA_MIRAGE_DIR"/*/soma_c/pattern.soma.h
else
    echo "buffers: no ocamlfind with lwt, the native_handles check is skipped"
fi
echo "buffers: ok"
