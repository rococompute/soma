# Native OCaml in a unikernel

This program uses local OCaml helpers and the `digestif.c` library through
ordinary `.definition` files. Soma checks the declared types against the
actual OCaml values and links the C-backed SHA-256 implementation into the
MirageOS image. There is no WASM interpreter or host crypto service.

With the Mirage/Solo5 toolchain installed:

```sh
SOMA_MIRAGE_SWITCH=hvf soma build main.soma
opam exec --switch=hvf -- solo5-hvt --mem=256 -- main.hvt
```

It prints `native OCaml`, `42`, the SHA-256 hashes of the empty string and
`abc`, and `native crypto checks passed`. Only public test messages are used.
`dev/ocaml-mirage-check.sh` builds a temporary copy, boots it, verifies the
output, and checks that relocating the source reuses the dependency build.

`soma.toml` pins Digestif to 1.3.0. Mirage resolves and cross-compiles the
declared libraries and their C stubs. The local helper also uses Lwt's real
API. Libraries must support Solo5: Unix, dynamic loading and host process
facilities are unavailable. Local `.ml` files are copied automatically;
C stubs belong to the declared library packages, not arbitrary adjacent C
files. Declarations remain opaque to Soma proofs; type checking a binding
does not prove its implementation correct.

For `soma build --no-image`, install the declared `digestif.c` and `lwt`
libraries for the OCaml compiler running the check. This mode checks the
application and bindings against real library interfaces, then the generated
runtime against separate Mirage stand-ins. It does not test C linkage.
`dev/ocaml-mirage-check.sh --no-image` runs that check on this example.

The image cache groups native programs by their dependencies and exact
versions. Relocated checkouts reuse those libraries; obsolete copied modules
are removed, and image generation is serialized within each cache root to
prevent concurrent programs from overwriting one another's sources.
