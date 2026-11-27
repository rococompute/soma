# In-place equations for imported Source types

A client can reuse an existing native type while keeping every original
constructor or record field public in its normal extracted declaration:

```soma
From Soma Require Import Native OCaml.
Import producer.
Definition main := use_producer_types.
From Soma Require Import OCaml.
OCaml Native Type Equation main Reuse producer.kind As "Producer.kind".
OCaml Native Type Equation main Reuse producer.routes As "Producer.routes".
```

The owner must be the current Source's transparent main. The reused type must
be an imported checked inductive in main's dependency closure. Targets are
qualified native identifiers, not expressions; self references, duplicates and
unreachable types fail. The checker accepts single unindexed runtime blocks
with type parameters and monomorphic runtime payloads/fields. Proof/type-valued,
dependent, higher-rank (including through aliases), indexed and coinductive
shapes are rejected. A declaration erased or customized away by extraction
cannot silently satisfy an equation: both fresh implementation and interface
must actually print the same type name and parameter arity.

The existing MiniML type printer emits `type kind = Producer.kind = ...` or
`type ('a, 'b) routes = ('a, 'b) Producer.routes = { ... }` directly in the
original declaration's position. Constructors, labels, payloads, field order,
parameter names and field types come from that actual extracted declaration.
Ordinary native compilation checks that the target has the compatible complete
representation; a different field signature is rejected. This is the existing
native type-checking trust boundary, not a new logical native-law axiom.

No module wrapper, converter, record reconstruction, custom extraction constant
or native evaluator is introduced. Source terms, matching, projections and
value printing are untouched. The separate brand printer keeps its original
identity and initialization behavior; it is not redirected to the target's
brand. Equations apply only when their owner is selected as main, so importing
a client does not change another entrypoint's extraction.

The owner's semantic/ABI identity includes ordered source symbol/target/arity
metadata. Existing identities without equations are unchanged. New separate
library metadata leaves all previous descriptor layouts intact.
`native_type_equations.manifest` has header `soma-native-type-equations-v1`
and ten quoted fields: owner, Source path/hash, original symbol, target,
printed name, parameter arity, full program/interface hashes and equation ABI
identity hash. Consumers authenticate whole compiler products; no generated
OCaml is parsed or rewritten. Existing byte-authenticated producer cleanup
removes obsolete metadata.

`test-suite/misc/soma_native_extraction_type_equations.sh` uses the old independent
Python header-rewrite method solely as a test oracle over a complete baseline
compiler unit. Native and bytecode check entire interfaces in both directions,
all constructors, parameterized record fields, exact payloads/promises/context/
faults/cancellation, natural Weak ownership, exact call allocation and complete
unit/brand initialization allocation. It checks frontend failures, rejection of
an incompatible actual target, Source/product/ABI authentication, target-sensitive
identities, entrypoint scoping and stale metadata cleanup.
