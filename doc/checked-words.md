# Checked signed native words

`Soma.CheckedWord` connects `NativeWord.signed` and the computational
`Uint63Axioms.of_Z` encoder to `CheckedArithmetic`'s binary integer bounds.
It uses the 64-bit OCaml runtime's signed 63-bit range, from `-2^62` to
`2^62-1`. It adds no input-size limit, unary conversion or native adapter.

The general bridge proves in-range decode/encode round trips, encode/decode
round trips, decoding injectivity, signed comparison specifications, and
addition/subtraction/multiplication refinement when the mathematical result
fits. It does not assume an arbitrary mathematical result fits merely because
its operands are words.

The runtime API checks binary integers before encoding:

- `of_Z` succeeds exactly for a representable value and decodes to that value.
- `add`, `sub` and `mul` check the mathematical operation on decoded operands.
  Every successful result also equals the corresponding native operation.
  Overflow is rejected before the native wrapping operation can hide it.
- `advance position count` accepts exactly a nonnegative start/count with a
  representable mathematical endpoint. It returns that endpoint, advances by
  exactly the count and advances strictly for a positive count.
- `scaled_advance position count stride` additionally checks both signs before
  calculating the mathematical scaled endpoint. Zero count or stride needs no
  arbitrary upper bound on the other binary integer. A negative stride is
  still rejected, including when the product would be zero.

These APIs reject an unrepresentable exclusive endpoint. They do not establish
that a representable address belongs to a mapped or authorized buffer, or that
the compiler and runtime implement their specified word operations correctly.

## Explicit existing primitive laws

Unlike the pure `CheckedArithmetic` and `PageGeometry` results, the word bridge
uses existing Rocq primitive specifications. Its 25 checked results have an
exact per-theorem inventory in
`test-suite/misc/soma_checked_word.assumptions.json`. The union includes the
existing `Uint63Axioms` addition, subtraction, multiplication, comparison,
shift/bit, equality and encoding specifications, and the existing
`Sint63Axioms` signed comparison specifications. Each theorem uses only its
listed subset. Kernel primitive functions/types are listed there as well.
No new axiom is declared, and these are not claimed as assumption-free proofs.

The conformance fixture checks each complete assumption set independently.
Its Source client explicitly permits the needed laws in its sealed verification
policy; removing the encoding law is rejected by the native gate. A downstream
verified project must likewise inventory the actual laws its proofs use.

## Validation

`test-suite/misc/soma_checked_word.sh` performs 77,558 checks in each native and
bytecode backend against independent Int64 arithmetic and overflow guards. It
covers signed extrema, round trips, accepted native operations, rejected wrap,
pointer/count/stride combinations and binary inputs up to 1,025 bits. It checks
that a zero count with an enormous positive stride still succeeds, while a
negative stride is rejected.

Compiling modified Source rejects zero encoding, wrapping addition before the
check, the wrong endpoint and an omitted stride sign check at their respective
proofs. These checks support the implementation and extraction boundary; they
do not replace the mathematical proofs or eliminate the stated primitive TCB.
