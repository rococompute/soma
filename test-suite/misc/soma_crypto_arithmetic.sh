#!/usr/bin/env bash
# Cross-check actual extracted limb addition and multiplication against
# Zarith on carry boundaries and deterministic, multi-limb random inputs.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export XDG_CACHE_HOME="$WORK/cache"
cd "$WORK"
cat > driver.definition <<'SOMA'
OCaml Library "zarith".
check : (string -> string -> string) -> (string -> string -> string) -> string.
SOMA
cat > driver.ml <<'OCAML'
let number s = if s = "" then Z.zero else Z.of_string ("0x" ^ s)
let check plus times =
  let fixed = ["00"; "01"; "7fffffff"; "80000000"; "ffffffff";
    "3fffffffffffffff"; "4000000000000000"; "7fffffffffffffff";
    "ffffffffffffffff"; String.make 128 'f'] in
  let check a b =
    let x = number a and y = number b in
    assert (Z.equal (number (plus a b)) (Z.add x y));
    assert (Z.equal (number (times a b)) (Z.mul x y)) in
  List.iter (fun a -> List.iter (check a) fixed) fixed;
  let state = Random.State.make [|631|] in
  let hex bytes = String.init (2 * bytes) (fun _ -> "0123456789abcdef".[Random.State.int state 16]) in
  List.iter (fun bytes -> for _ = 1 to 20 do check (hex bytes) (hex bytes) done)
    [1; 4; 8; 16; 32; 128; 256];
  "PASS extracted 31-bit limb addition and multiplication agree with Zarith"
OCAML
cat > main.soma <<'SOMA'
Require Import Crypto.
From Corelib Require Import PrimInt63.
Import driver.
hex (text : string) := match bytes_of_hex text with Some bytes => bytes | None => [] end.
plus (a b : string) : string :=
  let a := hex a in let b := hex b in
  hex_of_bytes (Bignum.to_bytes (S (length a + length b))
    (Bignum.add_carry (Bignum.of_bytes a) (Bignum.of_bytes b) 0%uint63)).
times (a b : string) : string :=
  let a := hex a in let b := hex b in
  hex_of_bytes (Bignum.to_bytes (length a + length b)
    (Bignum.mul_big (Bignum.of_bytes a) (Bignum.of_bytes b))).
main := check plus times.
SOMA
soma run main.soma > run.log 2>&1 || { cat run.log; exit 1; }
cat run.log
grep -q '^PASS extracted 31-bit limb' run.log
