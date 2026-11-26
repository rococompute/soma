# Source-owned local assemblies

A Source program can declare the public pattern for a lexical assembly:

```soma
From Soma Require Import Native OCaml.
Definition body := Native.Export (Native.Return (7, true)).
Definition main := body.
OCaml Native Assembly body As "(count, ready)".
```

Soma emits the complete `main.assembly` fragment around the fresh extracted
program, checked interface and native bindings. A build driver can insert its
bytes into the original compilation unit, retaining lexical primitive names
and native literal pooling. The driver does not supply an OCaml wrapper or
reconstruct the public declaration. `SOMA_OCAML_BINDINGS_MODULE` retains its
existing validated binding-namespace selection.

Patterns accept distinct OCaml value names, `_`, nested tuples matching the
checked product type, and complete record field puns for a declared native
record alias. Native flat triples, quadruples and quintuples retain their
arity. Partial or erased record fields, mixed or incorrect qualifications,
wrong tuple shapes, duplicate names and arbitrary expressions are rejected.
An assembly belongs to a separate transparent definition in its own Source
namespace; its already defined `main` must select that same checked value.
`main` itself is reserved for the extracted executable entry point. There is one
assembly per namespace. Its result is used once, without an extra runtime
interpreter, adapter or evaluator. Generic scalar exports retain their
polymorphism; existing static-module publication remains a separate facility.

`native_assemblies.manifest` begins with `soma-native-assemblies-v1`. Each
quoted row records the owner symbol, Source file/hash, assembly file/hash,
fresh program/interface/bindings hashes, layout identity hash and checked
owner contract. The contract is captured at the same Source checking phase as
`soma hash`, before library closure changes module-local references. The
parsed pattern participates in the semantic and native ABI identities; it
does not replace the checked body/type in the hash. Imports retain assembly
metadata, while only the selected main namespace produces its fragment.
Projects without assembly declarations retain their previous artifacts and
contracts. Producer-owned stale cleanup includes the new artifacts and
preserves edited files.

Some public functions deliberately have an eta wrapper in the original
compilation unit. They must retain that function object's identity and native
call shape rather than borrow the provider directly. A `.definition` can
request this explicitly:

```soma
OCaml Native Callable positional := string -> string.
OCaml Native External Eta Function closed : string -> string :=
  "Target.invoke" Using positional.
```

This checks the same required argument/result types and label/default schema
as `External Defaulted Function`, and emits a closed eta expression around
the typed provider. Optional defaults are omitted at full invocation; required
labels are supplied there. Native and bytecode closure sharing follows the
original OCaml expression. `External Defaulted Function` retains its existing
typed-coercion behavior for borrowing an already positional function. The
explicit eta operation has a distinct semantic/ABI identity; existing native
operation tags and descriptors are unchanged. The positional-default fixture
also checks both forms, exact promises, optional lookup phases, sharing,
provider identity distinctions and getter/public-call allocation.

`test-suite/misc/soma_native_assembly.sh` exercises native and bytecode
initialization, physical identity, literal sharing, generic inputs, native
record exports, caller context, exact promises, cancellation, synchronous and
initialization faults, exact public-call allocation, natural Weak lifetimes,
invalid patterns, semantic/ABI fingerprints and safe stale cleanup. Kykeon's
migration also compares the former assembly renderer against fresh compiler
output and runs the unchanged public assembly fixtures.
