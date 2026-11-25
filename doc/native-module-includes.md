# Native module includes

Existing native layout/provider members can be published in the current scope
without redefining their types, exceptions, functions or mutable state:

```soma
From Soma Require Import Native.
Module Header.
OCaml Native Module Alias Provider := "Target.Core".
OCaml Native Module Include layout := "Provider".
OCaml Native Module Alias Nested := "Inner".
End Header.
Definition main := (Header.Provider,Header.layout,Header.Nested).
```

`layout` is a Source dependency marker with a canonical logical `unit` body;
it adds no axiom or logical evaluator for the native module. The generated
native declarations are exactly `module Provider = Target.Core`,
`include Provider`, then `module Nested = Inner`. An include exposes the same
complete module members as the original native include. It does not wrap
functions, duplicate exception constructors, instantiate functors or rerun
provider initialization. The native compiler checks that the module exists
and supports inclusion.

Generated binding interfaces use
`include module type of struct include Provider end`, strengthening abstract
types to the original provider's types. A bare `module type of Provider` can
lose these equations for abstract types and is deliberately not used. Nested
types, exceptions, labelled/generic functions and mutable members retain their
original identities.

Aliases and includes share declaration order within each Source namespace;
different namespaces remain independent. A scope containing an include has a
`.exports` file with the exact native implementation declarations and a
`Soma_modules_<namespace hash>` binding namespace. Its
`native_module_declarations.manifest` rows authenticate kind (`alias` or
`include`), symbol, namespace, Source file/hash, artifact/hash, marker name,
target and ordinal. Kind, target, name, namespace and order participate in ABI
and semantic fingerprints, including the selected program's contract. An
alias-only scope retains its previous `.exports`, interface text and
`native_module_aliases.manifest` format byte-for-byte.

Only uppercase native module identifiers and dotted module paths are accepted
as targets. Arbitrary expressions, applied functors, spaces and invalid paths
are rejected. Missing native targets fail native compilation. Included member
name conflicts have the same native compiler behavior as the corresponding
ordinary OCaml declarations. Generated namespace names retain existing
collision checks.

`test-suite/misc/soma_native_module_include.sh` checks native and bytecode raw
exports and standalone namespaces, complete signature packaging, abstract and
nested type equations, scoped member names, declaration order, functor
applicativity/generativity, exact functions/state/exceptions, canonical unit
markers, initialization counts, natural Weak owners, generic values, borrowed
promises/context/cancellation and exact call allocation. It also checks
Source/product hashes, changed include/alias target fingerprints and rejection
of invalid/missing targets. Existing alias-only and non-module fixtures retain
all products and complete contract hash reports in cold extraction checks.
