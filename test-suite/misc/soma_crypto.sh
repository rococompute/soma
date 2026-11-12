#!/usr/bin/env bash
# Soma.Crypto run as OCaml. SHA-256: a binary (soma build, with a module
# that prints) hashes strings up to 14 MB, in tail calls at an 8 MB stack,
# each digest as the system's sha256 tool computes it. RSA: Cryptokit's
# signatures, below. And a Sandbox
# program that hashes type-checks as a MirageOS project (soma build
# --no-image), so that images extract Rocq's 63-bit integers
# (uint63.ml). The kernel checks FIPS 180-4's vectors when Soma is built
# (Crypto.v's Examples).
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
export SOMA_MIRAGE_SWITCH=nonexistent
cd "$WORK"

if command -v sha256sum > /dev/null; then sha() { sha256sum | cut -d' ' -f1; }
else sha() { shasum -a 256 | cut -d' ' -f1; }; fi

cat > out.definition <<'DEF'
print_text : string -> unit.
DEF
cat > out.ml <<'ML'
let print_text s = print_endline s
ML
cat > hashes.soma <<'SOMA'
Require Import Crypto.
Import out.

Fixpoint double (n : nat) (s : string) : string :=
  match n with O => s | S n => double n (s ++ s) end.

main := print_text (Crypto.sha256 "abc" ++ " " ++ Crypto.sha256 "" ++ " "
  ++ Crypto.sha256 (double 6 "0123456789") ++ " " ++ Crypto.sha256 (double 21 "abcdefg")).
SOMA
soma build hashes.soma > build.log 2>&1
got=$( (ulimit -s 8192; ./hashes.exe) )
# 640 and 14680064 bytes: 0123456789 doubled 6 times, abcdefg 21 times
# (yes ends on SIGPIPE)
repeat() { (set +o pipefail; yes "$1" | tr -d '\n' | head -c "$2"); }
want="$(printf abc | sha) $(printf '' | sha) $(repeat 0123456789 640 | sha) $(repeat abcdefg 14680064 | sha)"
if [ "$got" != "$want" ]; then
    echo "SHA-256 differs from the system's: got $got, want $want" >&2
    exit 1
fi

# RSA: a 2048-bit key of Cryptokit's (RSA.new_key, a random public
# exponent; generated for this test) and its PKCS #1 v1.5 SHA-256
# signatures of "hello" and "", as Cryptokit's sign_CRT made them:
# verified, refused for another message or a changed signature, and made
# again, the same bytes.
cat > rsa.soma <<'SOMA'
Require Import Crypto.
From Corelib Require PrimInt63.
Import out.
hex (s : string) : list PrimInt63.int := match bytes_of_hex s with Some l => l | None => [] end.
k_n : list PrimInt63.int := hex "7c8640089e1b03f79667290f6c876d2679a1bee57cc814e082c35fa6f46502bf0e277b7ea002ba50f5629781969b6bae194db4d05f7e95fb13930e704b99e1e8d339103fdf2ea2e45656191e76c1dd5f57c91ca8b80c64e00e4ceabcb93e67b9d77c8c58db98055798ea2a17a4060d3808da787e3f5b924c4fbf47569737d1c91fa3ad30707c8152de6a1e98d5dd4e7d92314496d3140ac36ccdaf470e7631652e60eadfd1668d528147a9dd7ce355b7ea56ba0285135749690e993b3ac7e64d5cb2a7e00af562254878a38b3adf5d0f8b5e3fe58da4b71ca8817e90f2db836d27a46db4b4af1b01e33f8138d5ee1c11c5d412158d24654c7a302fee0b83f1cd".
k_e : list PrimInt63.int := hex "aa9c8d0c1e11193fb16f798a6677b99cc56605676da7bfc7a062e44548d32d86ffa1eb5878948742ba57b333d30af20616d0a3f90eaf8eba04e0ce981c6a87908696f06fd5e33dfb0241cd80ed1b9571066cc95e9a991d871dc8bf079043550ea8267af4d9c1d6a9c3ce117a076c686f3c3097ced5a621bbad573d3991a5a7a528b30beab4835624347119da82043de0f8174a37e449b01eaf8d6a52c1b351af6a3d33e5bb919f39f78aab6bd54fea94e050a48ff73f9e5a78128949b0cfa453a9fbd89e60734370ac6ea2473e0719e510b7a3b175802aa0fc9d03ceb91ca943ea881dbc61788d95f2da2291eb4b7f0ae96991e6a00666ae0cbb46a28c7f533d".
k_p : list PrimInt63.int := hex "b2c1b55df879d700c0c743f13a559045ff1b5c8c3d523336fe7b6f83fca5d1d5e6fecd9644eec1f126893e484ae540ca88660fc7ecd42e38f0677883ab37e400da940d402aefb4dcfb463b08ccdf068c8d9d2a37b28909d4db2cc1302a3db49de024ef4549f8d3cc3cc2eb78997285ca64f6c7788d757b1ae0d725d4cb7679fd".
k_q : list PrimInt63.int := hex "b2554cc66c15579932465ebb852b8a5a8abc1a6b1455297678f8b79ed9ccaaed5f15396765e959aae3570a972f4d0725793fdc3bd6c93852cebae14b4480b5ffdf284af4724770e61bf74c48e5a7b85ce277814ceaa76cff3d8886730fc215702918fcdde3a067dc5a85705e631dab82b2bf4446339abd2912d85604da58b811".
k_dp : list PrimInt63.int := hex "29883be5876bb97fe186dd847b1f219f79fdc56735cf6a71cd36a770a04c852864729ee3bd538ed0be03768bfd3e5006f94d2b215b7bf40896583aea2becf5127867e470f2acf59133a46a93783b98d6390ed9da5f100e48476e7e39e322a0768083435ba01ce727a4e991c53fa77d52970d2acda67b0f0c4fe8ac6bfb311109".
k_dq : list PrimInt63.int := hex "72f0ba555f614ae059b787715d79ce4c3dff09ba846f7baf2e9b95814dd982524ac280c753eecba836d243d7fae928feacd02df759d84f2dd443b65b07581bdf40a1a4892d23f35f0c525403bc7f7aec16fca534d2993de781c483813c76710fc657d98f62a2b4b7509a1882e515a624816ff048d5e9b76450b2c1711dcd7045".
k_qinv : list PrimInt63.int := hex "6683ab07d885721ad8f945703f9e360dc9cfd898d96432fe5a0101d989627ff775fb1bc120b6478ce4a3986c45c55a23bc7bf25b596e66c1868381c6259d0713d09b965968f51f83a9bbdcebeef456872e0e15f70249ec6554d5a9a2f284bbbade4a3a85b0a8458db5fd516602257d1e6370c60e8446befa5757b3dea15091f5".
sig_hello : string := "6b2d2d8d7ae67c13e583ac6e8f8e024a380b43e0117de0b858bc9552c675e2c752028064376464c6a53f1276cfd988c7b6fdc468042b27b28a6ba53d001a0a0771006359383c3a86d4aeda310cd8149552911e0bcbcbc5da0787ac0ece12fa600a91cc9b746451435cbb71561bb665e4afca296aa545356b1667217bf83f340dd4a839efa4925bb5063db34e919035762276e2062ec197da5b7a974ab3826c5b9e6ec93e6974617352bc780cc051275c7e352ad232feb18cc6256ae2ab6b13908b39bae4028c78f24e97d02b1b3f99764a60c2a457d11ca016c960d8ebe55a9c88c1ff734e4abc2a971758ef4eff102cdc3aca684d9775ac0e1c01a3af5c19f4".
sig_empty : string := "2cf4088c6c8200dec19987573e1eff5a8ccba0a4ae8e3f16e1b0ee9f4ff8dd3c5ee32934846fad9be84de5f874d8f04218b02618dcea4cdbcb64ea5877fa8345714687c99afbf5adaea89525fdfb48602e47eccc0730fea3bca189d54f485166909d78606fc29dd56277cc647f20df4146f29c62931afd322981e325cbd7ada2e1b30176a864e842c7ea333c0eb3098bfcbab5de281128ebb80206b0086eed2c3f223c50a5a8def1748f99233d029621862bfde26dacaa0880e76311c6b325c4c528bc8ebf13834d855a1df1108900ade1b6800d8f8e75098457050f210e043f80bfc2a3ff2b1560fc6045ac4ddd58b407c23e372ee229e9126815c2de29bd2f".
verify (m sg : string) : bool := rsa_verify 256 k_n k_e m (hex sg).
sign (m : string) : string := hex_of_bytes (rsa_sign 256 k_p k_q k_dp k_dq k_qinv m).
flag (b : bool) : string := if b then "yes" else "no".
main := print_text (flag (verify "hello" sig_hello) ++ " " ++ flag (verify "" sig_empty) ++ " "
  ++ flag (verify "hellp" sig_hello) ++ " " ++ flag (verify "" sig_hello) ++ " "
  ++ flag (verify "hello" ("0" ++ sig_hello)) ++ " "
  ++ flag (Stdlib.Strings.String.eqb (sign "hello") sig_hello) ++ " " ++ flag (Stdlib.Strings.String.eqb (sign "") sig_empty)).
SOMA
soma build rsa.soma > rsa.log 2>&1
got=$( (ulimit -s 8192; ./rsa.exe) )
if [ "$got" != "yes yes no no no yes yes" ]; then
    echo "RSA differs from Cryptokit's: $got" >&2
    exit 1
fi

cat > image.soma <<'SOMA'
Require Import Sandbox Crypto.
main : io unit := print (Crypto.sha256 "abc") ;;
  print (if rsa_verify 1 (bytes_of_string "a") (bytes_of_string "a") "" (bytes_of_string "a") then "yes" else "no").
SOMA
soma build --no-image image.soma > image.log 2>&1
grep -q '(no image)' image.log
grep -q 'Uint63' "$SOMA_MIRAGE_DIR/plain/prog.ml"
test -f "$SOMA_MIRAGE_DIR/plain/uint63.ml"
