# Native operational semantics

`Soma.NativeSemantics` defines small-step execution directly over
`Soma.Native.program`, with `entry_runs` for the actual `Native.Export` boundary.
It introduces no alternate application syntax, evaluator or global axioms.
`step` changes a program and its heap by one transition; `steps` is its finite
reflexive/transitive closure. `diverges` describes an infinite sequence of
actual steps coinductively. Returned values and thrown exception objects are
terminal programs. A guarded proof establishes divergence of an unconditional
continuing loop, including when its result type has no terminating value.

## Implemented layer

The current rules cover `Bind`, `Invoke`, `Loop`, `Protect`, reference
allocation/read/write, vectors, text buffers, built-in faults, unary callback
allocation/calls and named callbacks.
Return and throw are terminal. A callback stores its checked program body and
receives its own newly allocated handle; calling it executes that body, rather
than treating the whole callback as an opaque result. Bind and exception
handlers propagate intermediate state changes. An exception raised before a
callback returns therefore retains earlier writes and its identity.

Heap cells retain their actual logical payload and function types. Lookup and
update are relations; no dynamic `Any`, unsafe cast, type-equality oracle or
untyped payload representation is used. Allocation gives an abstract fresh
identity. The heap invariant requires unique allocated identities below the
next-allocation counter. Reference writes preserve other addresses, identities
and well-formedness; allocation and complete executions preserve well-formedness
when foreign transitions preserve it. Arrays retain their header length across
updates. Storage writes preserve other addresses and other storage kinds;
complete executions preserve the runtime's object-size bounds and backend
profile when their foreign transitions do too.

Vectors have a canonical, unallocated empty handle and fresh nonempty arrays.
Element lookup and replacement interpret the signed 63-bit index before
conversion to a logical natural, so rejecting `max_int` or a negative index
does not construct a huge unary value. `Soma.NativeWord` proves both directions
of this bounds check, including negative, past-end and empty cases. Buffer
contents are byte strings; append and character insertion preserve aliases,
and contents snapshots retain their earlier value after subsequent writes.
Capacity is an allocation hint, rather than a semantic bound on contents.

The current storage profile is OCaml's 64-bit runtime: the array bound is
`2^54 - 1` elements and the string bound is `2^57 - 9` bytes. These are object
representation limits, not additional application input caps. Representable
allocations can still fail physically; memory exhaustion is outside this model.
Overflow faults have the corresponding runtime message and a fresh exception
identity. `Not_found` is a pre-existing singleton. Bounds faults preserve an
observed backend difference: native code uses its registered singleton;
bytecode allocates a fresh `Invalid_argument` on each failing safe-array call.
The world records the selected backend and owned transitions preserve it.

`foreign` describes individual `Invoke` calls, and `named` describes external
named callbacks. Both relations have typed arguments/results and explicit
before/after worlds. Either can raise after changing state. They are parameters
of the semantics, not global axioms or an arbitrary interpreter for owned
programs. A client must discharge the relevant native implementation laws;
an assumed snapshot law does not establish that an actual mutable table
implements that snapshot.

`loop_has_terminating_execution` requires a heap/state invariant, finite execution of the actual
step program and a decreasing natural measure on each continued state. It adds
no runtime fuel or input limit. A successful iteration can change the heap.
This proves existence of a successful execution (weak normalization), not
termination of every execution or universal loop correctness. Foreign relations
can admit more than one outcome; universal theorems must constrain and cover
all of those transitions.

The checked programs include a generic reference write/read roundtrip and a
newly allocated callback which writes, throws, and is caught by a handler that
observes both the new value and the exact original exception. These are
operational proofs over the actual constructors. Further proofs cover vector
replacement, buffer append/readback, empty-vector identity, fresh faults,
unchanged array headers, storage bounds, backend preservation and heap frames.
The contract-assumption fixture checks 51 semantic results and five checked-index
results. The word interpretation exposes the existing kernel primitives
`PrimInt63.int`, `sub`, `ltb`, `eqb`, `land`, `lor`, `lsl` and `lsr` to
`Print Assumptions`; these eight names are explicitly inventoried in the
fixture. No arithmetic specification axiom from `Uint63Axioms` or
`Sint63Axioms`, proof-irrelevance axiom or gradual evidence is introduced.

## Scope still open

Tables, general string/path/word operations, multiargument/pure
callbacks, borrowed scopes, promises and deferred scheduling still need rules.
An unsupported constructor is stuck; it is never silently evaluated by a
default rule. The current layer cannot establish progress for an arbitrary
Native program, or for a forged/unallocated handle.

Physical allocation costs, native/bytecode GC and lifetime observations,
resource exhaustion, compiler correctness and native implementation refinement
are not established by this abstract heap. Its existence does not complete
Kykeon's full Native-semantics gap or verify the generated runtime.

The sibling Kykeon proof-only `soma/verification_descriptor_scan.soma` client
uses these rules with the real descriptor `execute_step` and `allocate_fd`
definitions. It constructs a successful finite execution returning the first
free candidate following a finite busy prefix, under an explicit exact
membership law. Free-boundary preservation is checked separately as an
invariant. Universal execution correctness/termination and numeric lowest-fd
claims still need further proofs, machine-word no-wrap/range reasoning,
finite-table bounds and a proved connection to the actual fd table.

## Build and checking

The normal native theory-rule generator discovers `NativeSemantics.v` and
generates its dependencies and both installation layouts. Generated theory
Dune files remain untracked. Build/install through the ordinary Soma bootstrap,
then run `test-suite/misc/soma_contract_assumptions.sh` with `BIN` selecting the
installation. This checks the proof assumptions as well as compilation; it
rejects assumptions outside each group's explicit primitive inventory.

`test-suite/misc/soma_native_storage_semantics.sh` extracts actual storage entry
points and checks them under native and bytecode OCaml. It checks 162 signed
index cases per backend (including both signed extremes), aliases, immutable
snapshots, empty arrays, unchanged lengths, byte-buffer behavior and exception
identities. Observed index results and actual runtime object limits become
Gallina computation obligations checked by the kernel. This is conformance
evidence for those observations, not a proof of compiler/runtime refinement.
The test's OCaml client is test-only; Python writes proof obligations, never
production OCaml.
