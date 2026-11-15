#!/usr/bin/env bash
# Boundary rejection and interoperability; generated keys never leave the process.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
python3 - "$ROOT/toplevel/somaHost.ml" "$WORK/soma_host.ml" "$ROOT/toplevel/somaRsa.ml" "$WORK/soma_rsa_stubs.c" <<'PY'
import pathlib, sys
s = pathlib.Path(sys.argv[1]).read_text().split('{soma|', 1)[1].rsplit('|soma}', 1)[0]
pathlib.Path(sys.argv[2]).write_text(s)
c = pathlib.Path(sys.argv[3]).read_text().split('{soma|', 1)[1].rsplit('|soma}', 1)[0]
pathlib.Path(sys.argv[4]).write_text(c)
PY
cat > "$WORK/test.ml" <<'ML'
open Soma_host
let check b = if not b then failwith "RSA regression failed"
let () =
  List.iter (fun size -> check (not (fst (rsa_new_key size))))
    ["0x800"; "+2048"; "2_048"; "0"; "512"; "1024"; "2047"; "8193"; "999999999999999999999"; "bad"];
  let parts = match rsa_new_key "2048" with
    | true, (_, parts) -> parts | _ -> failwith "key generation failed" in
  match parts with
  | [size; n; e; d; p; q; dp; dq; qi] ->
    let pub = [size; n; e] and priv = [size; n; e; p; q; dp; dq; qi] in
    let msg = "tx\000chain\000binary\255\000payload" in
    let signature = rsa_sign priv msg in
    check (String.length signature = 512);
    check (rsa_verify pub msg signature);
    Gc.full_major ();
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
    (* Valid composite exponents and legacy full-width random exponents
       must retain the old signature bytes; no insecure fallback. *)
    let legacy label (k : Cryptokit.RSA.key) =
      let enc = rsa_encode in
      let fields = ["2048"; enc k.n; enc k.e; enc k.p; enc k.q;
                    enc k.dp; enc k.dq; enc k.qinv] in
      let sg = try rsa_sign fields msg with _ -> failwith ("legacy import rejected: " ^ label) in
      check (sg = enc (Cryptokit.RSA.sign_CRT k encoded));
      let public = ["2048"; enc k.n; enc k.e] in
      check (rsa_verify public msg sg);
      check (not (rsa_verify public (msg ^ "!") sg));
      check (not (rsa_verify public msg (enc k.n)));
      let malformed block =
        let forged = enc (Cryptokit.RSA.sign_CRT k block) in
        check (not (rsa_verify public msg forged)) in
      let replace_at at c = let b = Bytes.of_string encoded in Bytes.set b at c; Bytes.to_string b in
      malformed (replace_at 3 '\254'); (* PS must be entirely FF *)
      malformed (replace_at (256 - 51) '\049'); (* wrong DigestInfo tag *)
      malformed (replace_at 255 (Char.chr ((Char.code encoded.[255]) lxor 1)));
      malformed ("\000\001" ^ String.make 7 '\255' ^ "\000" ^ String.make 246 '\000');
      check (rsa_sign priv msg = signature) in
    (* Force e > n within the legacy 2048-bit field, independent of RNG luck. *)
    let zp = rsa_hex p and zq = rsa_hex q in
    let phi = Z.mul (Z.pred zp) (Z.pred zq) in
    let rec coprime e = if Z.equal (Z.gcd e phi) Z.one then e else coprime (Z.sub e (Z.of_int 2)) in
    let large_e = coprime (Z.pred (Z.shift_left Z.one 2048)) in
    check (Z.compare large_e (rsa_hex n) > 0);
    let zd = Z.invert large_e phi in
    let raw width z = rsa_decode (rsa_to_hex width z) in
    legacy "e greater than n" {key with e = raw 256 large_e; d = raw 256 zd;
      dp = raw 128 (Z.erem zd (Z.pred zp)); dq = raw 128 (Z.erem zd (Z.pred zq))};
    legacy "e=9" (Cryptokit.RSA.new_key ~e:9 2048);
    legacy "full-width random e" (Cryptokit.RSA.new_key 2048);
    (* Soma's generator need not order its primes. *)
    let swapped = [size; n; e; q; p; dq; dp;
      rsa_to_hex 128 (Z.invert (rsa_hex p) (rsa_hex q))] in
    check (rsa_sign swapped msg = signature);
    print_endline "ok host RSA validation, blinding-compatible determinism, Cryptokit interoperability"
  | _ -> failwith "wrong key shape"
ML
cd "$WORK"
opam exec --switch="${SOMA_OCAML_SWITCH:?set the runtime switch}" -- \
  ocamlfind ocamlopt -w -52 -package unix,zarith,cryptokit \
  -linkpkg -ccopt -Wall -ccopt -Wextra -ccopt -Werror \
  soma_rsa_stubs.c soma_host.ml test.ml -cclib -lcrypto -o test.exe
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
# Exported projects must carry the native binding and system dependency too.
soma extract main.soma -o exported > export.log 2>&1 || { cat export.log; exit 1; }
[ -f exported/soma_rsa_stubs.c ]
grep -q '"conf-libssl"' exported/*.opam
opam exec --switch="$SOMA_OCAML_SWITCH" -- dune build --root exported --profile release \
  > exported-build.log 2>&1 || { cat exported-build.log; exit 1; }
./exported/_build/default/soma_main.exe > exported-result.log
grep -q '^ok host bindings' exported-result.log
echo 'ok exported OpenSSL host project builds and runs'

# Refuse a reachable machine crypto operation before image extraction.
cat > blocked.soma <<'SOMA'
Require Import Sandbox.
Require Soma.Host.
main : io unit := print (Host.rsa_sign [] "not executed").
SOMA
for attempt in 1 2; do
  if SOMA_MIRAGE_DIR="$WORK/refused" soma build --no-image blocked.soma > blocked.log 2>&1; then
    echo 'FAIL machine RSA accepted in Sandbox'; exit 1
  fi
  grep -q 'no reviewed Sandbox RSA/entropy binding exists' blocked.log
done
[ ! -d "$WORK/refused/extract" ]
[ ! -e blocked.hvt ]
# Merely importing Host must not reject an unrelated Sandbox program.
cat > allowed.soma <<'SOMA'
Require Import Sandbox.
Require Soma.Host.
main : io unit := print "no host operation".
SOMA
SOMA_MIRAGE_DIR="$WORK/allowed" soma build --no-image allowed.soma > allowed.log 2>&1 || { cat allowed.log; exit 1; }
grep -q 'Mirage: checked' allowed.log
echo 'ok Sandbox rejects reachable host RSA before extraction, permits unused import'
