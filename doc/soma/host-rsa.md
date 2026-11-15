# Machine RSA boundary

Security-sensitive machine programs should use `Soma.Host.rsa_new_key`,
`rsa_sign`, and `rsa_verify`. The implementation delegates key generation,
key validation, SHA-256 and PKCS#1 v1.5 to Mirage Crypto. It explicitly enables
private-operation blinding and CRT hardening, and verifies the result before
returning a signature. The OS-backed Mirage RNG supplies generation and blinding
entropy; no caller seeds or deterministic fallback are accepted.

The generated runtime requires `mirage-crypto-pk` and
`mirage-crypto-rng.unix` (tested with 2.4.1), in addition to Unix. Install
`opam install mirage-crypto-pk.2.4.1 mirage-crypto-rng.2.4.1` in the runtime
switch. The compiler itself does not link these libraries. Every generated
Soma.Host module currently includes this dependency, including programs that
only use its other operations.

The API accepts decimal bit sizes from 2048 to 8192, multiples of 256, and
bounded, even-length hexadecimal unsigned big-endian integers. It accepts an
existing modulus one bit below its declared size, as older generators can
produce those keys. Generation fixes e = 65537. Keys retain the existing
`size,n,e,d,p,q,dp,dq,qinv` layout and fixed-width hex fields. Signing accepts
`size,n,e,p,q,dp,dq,qinv`; it derives d with the library, validates the supplied
CRT fields, and preserves either prime ordering. Mirage Crypto requires prime public
exponents for private-key import. Legacy Cryptokit random exponents may be
composite; those keys still verify but signing fails. Applications supporting
such keys must resolve this compatibility limitation before adopting this API. Signatures are lowercase hex,
SHA-256/PKCS#1 v1.5, one modulus-width long. Invalid verification returns false;
key generation returns a generic failure; signing raises a generic exception
and never substitutes an empty or reference-generated signature. Errors never
include key material. The application must retain its existing private-file
permissions.

This is an explicit trusted host dependency. It is not a proof of RSA security,
constant-time behavior for the complete application, safe memory erasure, or
resistance to every fault or side channel. Key import performs validation and
private-number arithmetic and is not claimed constant-time. It currently runs
on every signing call; performance and key lifecycle/caching need review before
production use. The machine integration uses Unix entropy; it does not supply a
Mirage unikernel entropy integration. Do not silently fall back to Soma.Crypto.

Soma.Crypto remains computational reference code. Its fixed twelve Miller–Rabin
bases do not establish an independent-random-base error bound for 1024-bit
candidates; that observation is not evidence of a composite key or compromise.
Its private exponentiation is not a hardened signing provider. Existing
examples establish only the stated computations.

Run `test-suite/misc/soma_host_rsa.sh` with `SOMA_OCAML_SWITCH` set to a runtime
switch containing these libraries and Cryptokit (test interoperability only).
The test checks bounds, malformed keys/signatures, both prime orders, binary
messages, deterministic output despite blinding, Cryptokit interoperability,
and the compiled Host bindings against the Soma reference. Generated private
keys remain in memory and are not logged or committed.

Provider reference: https://mirage.github.io/mirage-crypto/doc/mirage-crypto-pk/Mirage_crypto_pk/Rsa/index.html
