#!/usr/bin/env bash
# Boundary rejection and interoperability; generated keys never leave the process.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
python3 - "$ROOT/toplevel/somaHost.ml" "$WORK/soma_host.ml" <<'PY'
import pathlib, sys
s = pathlib.Path(sys.argv[1]).read_text().split('{soma|', 1)[1].rsplit('|soma}', 1)[0]
pathlib.Path(sys.argv[2]).write_text(s)
PY
cat > "$WORK/test.ml" <<'ML'
open Soma_host
let check b = if not b then failwith "RSA regression failed"
let () =
  List.iter (fun size -> check (not (fst (rsa_new_key size))))
    ["0"; "512"; "1024"; "2047"; "8193"; "999999999999999999999"; "bad"];
  let parts = match rsa_new_key "2048" with
    | true, (_, parts) -> parts | _ -> failwith "key generation failed" in
  match parts with
  | [size; n; e; d; p; q; dp; dq; qi] ->
    let pub = [size; n; e] and priv = [size; n; e; p; q; dp; dq; qi] in
    let msg = "tx\000chain\000binary\255\000payload" in
    let signature = rsa_sign priv msg in
    check (String.length signature = 512);
    check (rsa_verify pub msg signature);
    check (rsa_sign priv msg = signature);
    check (not (rsa_verify pub (msg ^ "!") signature));
    List.iter (fun bad -> check (not (rsa_verify pub msg bad)))
      [""; "00"; signature ^ "00"; String.make 512 'g'; String.make 512 '0'; n];
    List.iter (fun bad -> check (not (rsa_verify bad msg signature)))
      [[]; ["1024"; n; e]; [size; "00"; e]; [size; n; "00"];
       [size; String.make 4096 'f'; e]; [size; "-1"; e]];
    let rejects fields =
      match rsa_sign fields msg with
      | _ -> failwith "malformed signing key accepted"
      | exception Failure "RSA signing failed" -> () in
    rejects []; rejects [size; n; e; p; p; dp; dq; qi];
    rejects [size; n; e; p; q; "00"; dq; qi];
    rejects [size; n; e; p; q; dp; dq; "00"];
    (* Interoperate with the former Cryptokit wire encoding. *)
    let bytes = rsa_decode in
    let key : Cryptokit.RSA.key =
      { size = 2048; n = bytes n; e = bytes e; d = bytes d;
        p = bytes p; q = bytes q; dp = bytes dp; dq = bytes dq; qinv = bytes qi } in
    let digest = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) msg in
    let prefix = bytes "3031300d060960864801650304020105000420" in
    let encoded = "\000\001" ^ String.make (256 - 3 - String.length prefix - 32) '\255'
                  ^ "\000" ^ prefix ^ digest in
    check (Cryptokit.RSA.unwrap_signature key (bytes signature) = encoded);
    check (rsa_encode (Cryptokit.RSA.sign_CRT key encoded) = signature);
    (* Soma's generator need not order its primes. *)
    let swapped = [size; n; e; q; p; dq; dp;
      rsa_to_hex 128 (Z.invert (rsa_hex p) (rsa_hex q))] in
    check (rsa_sign swapped msg = signature);
    print_endline "ok host RSA validation, blinding-compatible determinism, Cryptokit interoperability"
  | _ -> failwith "wrong key shape"
ML
cd "$WORK"
opam exec --switch="${SOMA_OCAML_SWITCH:?set the runtime switch}" -- \
  ocamlfind ocamlopt -w -52 -package digestif.c,unix,mirage-crypto-pk,mirage-crypto-rng.unix,cryptokit \
  -linkpkg soma_host.ml test.ml -o test.exe
./test.exe
cat > soma.toml <<'TOML'
[project]
name = "host_rsa_check"
version = "0.1.0"
TOML
cat > main.soma <<'SOMA'
Require Soma.Host Soma.Crypto.
From Soma Require Import OCaml.
bytes (s : string) := match Crypto.bytes_of_hex s with Some b => b | None => [] end.
main : unit :=
  match Host.rsa_new_key "2048" with
  | (true, (_, [size, n, e, d, p, q, dp, dq, qi])) =>
    let sg := Host.rsa_sign [size, n, e, p, q, dp, dq, qi] "hello" in
    if Host.rsa_verify [size, n, e] "hello" sg &&
       Crypto.rsa_verify 256 (bytes n) (bytes e) "hello" (bytes sg) &&
       String.eqb sg (Crypto.hex_of_bytes (Crypto.rsa_sign 256
         (bytes p) (bytes q) (bytes dp) (bytes dq) (bytes qi) "hello"))
    then Host.print_lines ["ok host bindings and Soma reference interoperability"]
    else Host.print_lines ["FAIL host RSA interoperability"]
  | _ => Host.print_lines ["FAIL host RSA generation"]
  end.
SOMA
soma build main.soma > build.log 2>&1 || { cat build.log; exit 1; }
./main.exe > result.log
cat result.log
grep -q '^ok host bindings' result.log
