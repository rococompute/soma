# Native packed module types

A first-class native module can be carried as a typed opaque Source value:

```soma
From Soma Require Import Native.
OCaml Native Packed Module Type logger := "Logs.LOG".
OCaml Native External Value make_logger : source -> logger := "Logs.src_log".
```

The compiler validates a named module-signature path and constructs the native
package type `(module Logs.LOG)` internally. It does not accept arbitrary type
or module expressions, functor applications, signature constraints or code
fragments. Missing signatures fail native compilation. Source uses the existing
opaque native handle machinery; no new axiom, logical evaluator, cast or
runtime representation is added. Existing ordinary native type declarations
retain their previous output.

Packages may pass through typed Source functions or native callbacks. Native
interfaces retain their package type equation, allowing the host compiler to
check unpacking into the original complete signature, including abstract types,
polymorphic members, mutable state and exceptions. Package/member identities and
ownership remain those of the actual native value. The signature path
participates in existing native ABI and semantic fingerprints.

`test-suite/misc/soma_native_packed_module_type.sh` checks native/bytecode package
identity through a Source identity function, full signature unpacking, abstract
values, polymorphic members, shared mutable state, exception identities,
promises/context/cancellation, exact native faults, natural Weak ownership and
allocation. It rejects invalid/missing signature paths and checks changed
signature fingerprints. Existing native function exports, module declarations,
algebraic reexports and other regression fixtures remain unchanged.
