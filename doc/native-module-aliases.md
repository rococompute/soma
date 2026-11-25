# Native module aliases

A native provider namespace can be published without reproducing its members
or changing its nominal types:

```soma
From Soma Require Import Native.
Module Header.
OCaml Native Module Alias Provider := "Target.Core".
OCaml Native Module Alias Nested := "Provider.Inner".
End Header.
```

Each declaration has a canonical logical `unit` body, allowing checked Source
code to select the declaration and fingerprint its ownership without an axiom
or a logical evaluator for the native module. The native compiler emits the
exact equations `module Provider = Target.Core` and
`module Nested = Provider.Inner`. It does not copy structures, eta-wrap
functions, instantiate functors or evaluate providers. Targets must be
available to the native build, where OCaml checks the complete module paths and
interfaces.

Declarations retain their source namespace and declaration order. Aliases in
different Source namespaces can share public names. Standalone bindings expose
one `Soma_modules_<namespace hash>` namespace per scope; the generated interface
preserves the full alias equations. A `.exports` artifact contains the same
plain module equations for clients that embed them at existing lexical phases.
`native_module_aliases.manifest` authenticates the symbol, namespace, source
file/digest, artifact/digest, alias, target and order. Alias ownership, targets
and order participate in ABI and semantic hashes, including the selected
program's contract hash. Module alias tokens reduce only to `tt`; they do not
expose native module evaluation to the logical kernel.

Only valid uppercase OCaml module identifiers and dotted module paths are
accepted. Code fragments, functor applications and invalid paths are rejected.
Missing native modules fail native typechecking. Generated namespace names use
the same collision checks as other native generated names. C bindings reject
module-alias declarations.

`test-suite/misc/soma_native_module_alias.sh` checks native and bytecode exact
aliases in both standalone namespaces and raw exports. It covers declaration
order where alphabetic sorting would fail, duplicate names across scopes,
abstract/nested type equations, generic functions, shared mutable state,
exception constructors, first-class module identity, functor applicativity and
generativity, unchanged initialization counts, borrowed promises/context/
cancellation, exact allocation, source/product hashes and changed target
fingerprints. It also checks canonical logical bodies without new assumptions
and rejects invalid/missing module paths. Existing programs with no module
aliases emit no new artifacts or binding text.
