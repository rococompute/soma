# Machine RSA boundary

Security-sensitive machine programs use `Soma.Host.rsa_new_key`, `rsa_sign`,
and `rsa_verify`. The generated machine runtime links OpenSSL 3's default
provider through a small C binding; the compiler itself does not link libcrypto.
OpenSSL supplies key generation, OS-seeded randomness, private RSA with its
normal blinding and CRT protection, SHA-256 and PKCS#1 v1.5 operations. Every
signature is verified before release, including against the original public
exponent. Errors are generic and never contain key material. There is no
fallback to Soma.Crypto, deterministic entropy, or disabled blinding.

Build prerequisites: OpenSSL 3 headers and libcrypto (tested with 3.5.7), a C
compiler, Unix and Zarith. Generated projects declare `conf-libssl` in opam and
include `soma_rsa_stubs.c`; an older OpenSSL fails with an explicit compile-time
error. This currently adds the native dependency to every Soma.Host program,
including those using only other Host primitives. System include/link paths
must make OpenSSL available. This is the default provider, not a FIPS claim.

## Formats and validation

Sizes are four decimal digits: 2048 through 8192, multiples of 256. Hex integers
are unsigned big-endian, even-length and bounded; signatures must have exactly
the declared modulus width. An older modulus one bit below its declared size is
accepted. New keys use e = 65537 and retain `size,n,e,d,p,q,dp,dq,qinv` with the
existing fixed-width fields. Signatures remain lowercase hex SHA-256/PKCS#1 v1.5.
Signing accepts `size,n,e,p,q,dp,dq,qinv`; private import reconstructs d, then
OpenSSL's default-provider private and pairwise checks validate the factors,
modulus, exponent relation and supplied CRT fields before any private operation.
Verification rejects malformed input; key generation returns failure; signing
raises a generic exception instead of emitting an empty signature.

## Legacy exponents — explicit compatibility path

Cryptokit's older random public exponents can be composite and can exceed n.
Both can be mathematically valid RSA. Mirage Crypto's importer and OpenSSL's
SP800-56B public-key validation impose incompatible restrictions; this is not
evidence of compromised keys.

During private import only, the exponent is reduced modulo (p-1)(q-1), which
preserves the RSA transformation for the validated primes. d is reconstructed
using Zarith. The provider fully validates that normalized private key and all
original CRT fields. Original key files, identities and public exponents remain
unchanged. The emitted signature is also checked against the original key.

Ordinary verification uses EVP_DigestVerify. Where OpenSSL's EVP public
operation rejects a legacy exponent (e >= n, or a full-width exponent on a large
modulus), the explicitly selected compatibility verifier uses OpenSSL BN_mod_exp
on PUBLIC operands, OpenSSL's PKCS#1 type-1 padding checker, and OpenSSL SHA-256.
It requires the exact 51-byte SHA-256 DigestInfo encoding: no alternate hash,
noncanonical DER, trailing bytes, short padding or non-FF padding is accepted.
This public path does not perform private exponentiation. Its exported padding
checker is deprecated but available in OpenSSL 3; this glue and its continued
support require security/maintenance review. We do not bypass private-key
validation or fall back after an arbitrary EVP verification failure.

## Lifetime, performance and trust

Only the most recently validated private key is cached, avoiding repeated
primality/import checks for every vote. The cache is replaced before importing
a different key; invalid replacement input cannot reuse the prior key. It can
retain one key until process exit. Native handles are accounted to OCaml's GC
and freed by finalizers. Temporary C import buffers are cleansed, but no complete
secret-erasure guarantee is made for the OCaml heap or provider. Key import and
normalization are not claimed constant-time. Applications must retain private
file permissions and isolate the process. OpenSSL, Zarith, the C/OCaml binding,
compiler, entropy source and host are trusted; this is not a cryptographic proof.

Soma.Crypto remains computational reference code. Twelve fixed Miller–Rabin
bases do not establish an independent-random-base error bound for 1024-bit
candidates; no composite key or compromise was demonstrated. Its unblinded
private exponentiation is not used by this boundary.

## Unikernels

This boundary is for machine binaries. Sandbox/Mirage cannot link this Unix
host module, and Soma rejects reachable Host RSA before image extraction, with an explicit
missing-provider/entropy diagnostic. Unused imports remain allowed.
A production unikernel needs a separate vetted provider, reviewed device entropy
and compatible legacy-key import, plus cross-compilation and image tests. Do not
route private keys through the remote host service or silently use Soma.Crypto.
No such integration or deployment is claimed here.

## Checks

`test-suite/misc/soma_host_rsa.sh` compiles the C binding with warnings as errors
and checks input bounds, invalid CRT fields, cache replacement, binary messages,
e=9, full-width random exponents, an exponent guaranteed greater than n, both
prime orders, malformed padding/DigestInfo/digests, Cryptokit signature equality,
and compiled Host/Soma-reference interoperability. Keys remain in memory and
are never logged. The test additionally needs Cryptokit in SOMA_OCAML_SWITCH.

References: https://docs.openssl.org/3.5/man3/EVP_DigestSignInit/ and
https://docs.openssl.org/3.5/man3/EVP_PKEY_check/ . OpenSSL's default-provider
pairwise validation differs intentionally from its SP800-56B public-key check.
