# Native callable value reexports

A checked native callable description can be published as its actual typed
native value, preserving compiler information about closed functions:

```soma
From Soma Require Import Native Handles.
OCaml Native External Value target : forall A:Type,A -> promise A := "Lwt.return".
OCaml Native Static Invoke prepared : forall A:Type,A -> promise A :=
  target With [Argument 0] AtFullApplication.
OCaml Native Reexport Value ret := prepared.
```

The declaration belongs in a `.definition` file. `ret` is a canonical logical
unit marker with an explicit dependency on the already checked getter. No new
axiom or native logical evaluator is introduced. The native export is the
producer's typed function expression, rather than a function recovered through
an opaque effect export. This distinction can matter even when returned
function objects and direct call allocation match: hiding the compiler's
closure approximation can force a surrounding caller to allocate an extra
closure for every composed call.

Reexports accept unit getters for checked Static Invoke descriptions or
borrowed function values. Arbitrary expressions, scalar getters, non-native
references and native operations requiring runtime arguments are rejected.
Types, generic parameters, labels and expression trees have already been
checked by the getter declaration; the emitted value retains its complete
polymorphic type annotation. The original producer module context is retained
for relative native references. No getter is called per invocation and no
replacement adapter or interpreter is introduced.

Each namespace has a `Soma_values_<namespace hash>` native binding namespace
with a checked interface and a raw `.exports` artifact. Declaration order is
retained. `native_value_reexports.manifest` authenticates symbol, namespace,
Source file/hash, artifact/hash, public name, owner and ordinal. The complete
producer descriptor, ownership, module context and order participate in ABI
and semantic fingerprints, including the selected program's contract.
Programs without value reexports retain their earlier products unchanged.

`test-suite/misc/soma_native_value_reexport.sh` checks native and bytecode raw
exports and standalone bindings, borrowed bind function identity, independent
generic domains/results, function and byte payloads, closed-function sharing,
exact promises/faults/context/cancellation and natural Weak ownership. Its
allocation oracle includes a caller that creates a bind callback using the
published return function, detecting the 32-byte native closure regression
that motivated this capability. It also checks canonical markers, invalid
sources/getters, provenance and changed target fingerprints.

For scalar, cell or immutable-data aliases, use
[`Reexport Binding`](native-binding-reexports.md). `Reexport Value` retains
its existing callable-only checks.
