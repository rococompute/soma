# Native operational semantics

`Soma.NativeSemantics` defines small-step execution directly over
`Soma.Native.program`, with `entry_runs` for the actual `Native.Export` boundary.
It introduces no alternate application syntax, evaluator or global axioms.
`step` changes a program and its heap by one transition; `steps` is its finite
reflexive/transitive closure. Returned values and thrown exception objects are
terminal programs.

## Implemented layer

The current rules cover `Bind`, `Invoke`, `Loop`, `Protect`, reference
allocation/read/write, unary callback allocation/calls and named callbacks.
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
when foreign transitions preserve it.

`foreign` describes individual `Invoke` calls, and `named` describes external
named callbacks. Both relations have typed arguments/results and explicit
before/after worlds. Either can raise after changing state. They are parameters
of the semantics, not global axioms or an arbitrary interpreter for owned
programs. A client must discharge the relevant native implementation laws;
an assumed snapshot law does not establish that an actual mutable table
implements that snapshot.

`loop_terminates` requires a heap/state invariant, finite execution of the actual
step program and a decreasing natural measure on each continued state. It adds
no runtime fuel or input limit. A successful iteration can change the heap.
The theorem does not assert that arbitrary loops terminate.

The checked programs include a generic reference write/read roundtrip and a
newly allocated callback which writes, throws, and is caught by a handler that
observes both the new value and the exact original exception. These are
operational proofs over the actual constructors. The contract-assumption
fixture checks all 17 exported theorems; only the existing `PrimInt63.int`
primitive type is allowed.

## Scope still open

Vectors, tables, text buffers, string/path/word operations, multiargument/pure
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
definitions. It proves termination at the first free candidate following a
finite busy prefix, under an explicit stable-membership law. Numeric lowest-fd
claims still require machine-word no-wrap/range reasoning, finite-table bounds
and a proved connection to the actual fd table.

## Build and checking

The normal native theory-rule generator discovers `NativeSemantics.v` and
generates its dependencies and both installation layouts. Generated theory
Dune files remain untracked. Build/install through the ordinary Soma bootstrap,
then run `test-suite/misc/soma_contract_assumptions.sh` with `BIN` selecting the
installation. This checks the proof assumptions as well as compilation; it
rejects added axioms, proof-irrelevance escapes or gradual evidence outside the
existing primitive type whitelist.
