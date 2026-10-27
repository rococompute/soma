# Stdlib

Rocq's standard library, vendored so that Lightlang programs can use it with
`From Stdlib Require ...` and no extra flags.

- Source: https://github.com/rocq-prover/stdlib, tag `V9.2.0`, commit
  `8dd155bc10529814202f8f4c643e5ae6c2c88fa6` (LGPL-2.1, like Rocq).
- Only the `.v` files of its `theories/` directory are copied, without
  `All.v`. The files are unmodified.
- Built by the generated `theories/Stdlib/dune` (`make dunestrap`), with
  `-boot`, so as plain Rocq without the Lightlang prelude, and with the
  warning flags of its `theories/_CoqProject`. Installed in
  `user-contrib/Stdlib`.

To upgrade, replace these files with the `.v` files of a newer tag, update the
tag and commit above, and run `make dunestrap`.
