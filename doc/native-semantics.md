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
allocation/read/write, vectors, text buffers, string length/index/slices,
built-in faults, unary callback allocation/calls and named callbacks.
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

## Universal total correctness

`Soma.NativeTotal` adds `total` over the same `step`/`steps` relations. It
requires both accessibility of **every** successor and progress or a satisfied
terminal postcondition at **every** reachable configuration. A program with no
applicable rule therefore fails the progress obligation; it cannot be certified
merely because it has no infinite executions.

`ranked_total_correctness` constructs this judgment from a preserved invariant,
a natural rank decreasing on every actual transition, and progress or a
satisfied result/exception postcondition throughout the invariant. The rank is
a mathematical proof measure, not executable fuel. `ranked_execution_length`
bounds any finite transition sequence by the starting rank. Accessibility can
also be supplied directly, permitting well-founded relations other than a
single natural-valued measure.

The judgment is preserved by each actual step, excludes coinductive divergence,
guarantees a finite result/exception execution and requires every finite
maximal execution to satisfy the postcondition. Its foreign-call rules account
for **every** permitted return and exception, including the resulting world.
A negative theorem shows that an allowed false return rejects a true-only
specification, even if a successful true-returning path also exists. Other
negative theorems reject a spinning loop and an unsupported table
operation. Return and throw satisfy total correctness exactly when their
specified outcome meets the postcondition.

`entry_total` applies the same judgment at the actual `Native.Export` boundary;
it both provides an execution and checks the postcondition of every
`entry_runs` result or exception.

These 24 audited results provide a universal proof interface; they do not
supply the concrete invariants, progress and decreasing measures of Kykeon's
82 production loop sites.

`Soma.NativeControl` provides eight audited compositional results for actual
sequencing, primitive calls and loop iterations. The sequencing rule accounts
for all intermediate states and exception outcomes; primitive calls require
at least one permitted outcome and a contract covering every permitted
outcome. Loop unfolding is proved to cover every actual successor, and a
certified iteration can establish the contract of the resumed loop. Typed
constructor views avoid injecting existential type indices or assuming proof
irrelevance. The rules introduce no alternate application syntax or runtime
fuel.

The checked programs include a generic reference write/read roundtrip and a
newly allocated callback which writes, throws, and is caught by a handler that
observes both the new value and the exact original exception. These are
operational proofs over the actual constructors. Further proofs cover vector
replacement, buffer append/readback, empty-vector identity, fresh faults,
unchanged array headers, storage bounds, backend preservation and heap frames.
The contract-assumption fixture checks 51 semantic results and ten checked-index/span
results. The word interpretation exposes the existing kernel primitives
`PrimInt63.int`, `sub`, `ltb`, `eqb`, `land`, `lor`, `lsl` and `lsr` to
`Print Assumptions`; these eight names are explicitly inventoried in the
fixture. No arithmetic specification axiom from `Uint63Axioms` or
`Sint63Axioms`, proof-irrelevance axiom or gradual evidence is introduced.

## String primitives and spans

`Soma.NativeText` proves eleven results, including
universal total correctness for length, signed and natural indexing, slices,
and each corresponding failure outcome. Valid calls preserve the world and
return the specified byte contents. Index faults use the backend-specific
bounds identity; invalid slices allocate a fresh exception with the runtime's
`String.sub / Bytes.sub` message.

The supporting content lemmas establish that an in-bounds byte is defined,
that an accepted slice has exactly its requested length, and that every
natural cursor up to a representable string's end fits the extraction carrier.

`NativeWord.bounded_slice` checks signs and the whole span in `Z` before
converting either argument to a logical natural. Five checked results establish
soundness, completeness and rejection of negative or past-end spans. This
avoids wrapping `offset + count`, including at both signed extremes, and accepts
the empty slice exactly at the end. It introduces no additional input cap.

String payloads must satisfy the physical string representation bound. Natural
indices additionally require `NativeWord.nat_fits`, the signed OCaml carrier's
actual representability bound; otherwise the model supplies no rule. Clients
must discharge these premises. This does not prove that arbitrary Source
natural arithmetic refines machine integers beyond their representation range.

The model tracks string byte values, not physical string objects. For example,
OCaml 5.5's full-length `String.sub` returns its original input object. Runtime
conformance checks retain that behavior, but string identity/GC/allocation
refinement is not established by these content contracts.

## Scope still open

Tables, higher-order string mapping, path/word operations, multiargument/pure
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
definitions. Under an explicit exact, total, stable membership law and a
finite busy prefix ending at a free slot, it now proves universal total
correctness: every result is that first free candidate in machine-word
successor order, the world stays unchanged and execution cannot diverge.
Induction on the finite busy-prefix length supplies the decreasing measure.
The weaker finite execution witnesses remain separately named. The production
descriptor module also requires preservation of the first-free boundary under
its actual busy-slot scan decision; the proof client reuses that module's
proof-only boundary definitions.

This covers the descriptor scan entry under its premises, not every branch of
the descriptor executor or the other loop sites. Numeric lowest-fd claims,
existence of a free slot and the exact snapshot law still need machine-word
no-wrap/range reasoning, finite-table bounds and a proved connection to the
actual mutable fd table. No assumed provider contract is presented as an
implementation refinement proof.

## Build and checking

The normal native theory-rule generator discovers these source theories and
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

`test-suite/misc/soma_native_text_semantics.sh` extracts the real string entry
points and checks 1,393 observations per backend: signed extremes, binary
bytes, natural indices, valid/invalid spans and empty end slices. Runtime checks
also cover shared bounds identity, fresh substring faults and full-slice
identity relative to the installed Stdlib. The observed signed bounds and byte
contents become kernel-checked Gallina computation obligations. Python produces
only those test proofs, never OCaml.
