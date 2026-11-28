# Checked arithmetic and page geometry

`Soma.CheckedArithmetic` computes in binary `Z` before checking whether a
result fits the 64-bit OCaml profile's signed 63-bit carrier,
`[-2^62, 2^62-1]`. Checked addition, subtraction and multiplication return a
value exactly when their mathematical result fits. They do not first perform
a wrapping native operation and then attempt to detect overflow.

The checked span constructor requires a nonnegative beginning and length,
ordered endpoints and a representable exclusive endpoint. It returns a record
carrying those proofs. Scaled spans check `start + count * stride` in binary
arithmetic, with nonnegative count and stride. Slice lemmas bound callback
offsets and lengths by the original span length. The numeric limit is the
actual carrier limit; this library introduces no application input/fuel cap.
This is an endpoint-representation contract, not a claim that a span denotes
mapped guest memory or that every virtual-address policy must use this profile.

`Soma.PageGeometry` defines 4 KiB page bases, offsets and exclusive ends in
binary integers. A layout records the low window, COW window and high-region
boundary. Below paged regions, the next boundary is the earliest future
window edge. In paged regions it is the exclusive page end. Both cases are
proved to advance, even without assumptions that layout fields are sorted.
Taking the minimum with the checked span's end gives a positive chunk enclosed
by the request. Paged chunks cannot cross a page boundary; nonpaged chunks
preserve comparisons with every window edge. Remaining distance decreases.

The pure partition function uses a structural counter derived from the actual
span length. Its sufficiency is proved. A `covers` specification states exact
consecutive coverage with positive, boundary-enclosed chunks; the returned
partition satisfies it, its lengths sum to the requested length, and all
callback offsets/counts remain in bounds. The partition is a specification and
testable Source implementation. It is not an instruction to eagerly allocate
all chunks before running effectful guest-memory callbacks.

The sixteen arithmetic and twenty-three geometry results are each checked by
`soma_contract_assumptions.sh` with an empty allowed-assumption set. Native and
bytecode extraction is exercised by `soma_checked_memory.sh`: 28,205 cases per
backend, using independent `Int64` arithmetic, bit masks, overflow guards and
coverage observations. Cases include signed extrema, zero/negative lengths,
scaled endpoints and page-end wrap at the last representable native page.
`soma_checked_memory_mutations.sh` rejects wrong addition, a nonforward page
end or region boundary, oversized pieces and an empty partition at the
corresponding proofs.

These libraries are not yet the Kykeon guest traversal implementation.
PrimInt63-to-`Z`/result conversion laws, the effectful traversal, raw memory and
page-table mapping refinement, native fault identity/propagation and compiler/
extraction correctness remain separate obligations. In particular, the Source
page formula avoids signed wrap; that alone does not prove that an existing
wrapping `PrimInt63.lor`/`add` implementation has the same result.
