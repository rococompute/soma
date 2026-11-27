# Whole checked literal declarations

Source may request a complete native constant declaration as an authenticated
artifact for insertion in an existing compilation unit:

```soma
OCaml Native Literal Declaration main From catalog.
```

The owner must be the transparent `main` of that Source. The selected value must
be a different transparent constant in the same Source and a checked dependency
of main. Duplicate requests are rejected. This declaration introduces no logical
axiom, executable primitive, native law, converter, wrapper or runtime module.

The real OCaml printer captures the entire existing `let` declaration and its
entire `val` signature, using their actually allocated names and native types.
The complete ordinary program is unchanged. The implementation must consist of
closed native constant syntax: native characters/strings, native booleans/unit,
and literal lists, options and pairs built from them. Their complete signatures
must also use only self-contained native types and generic type variables;
an empty list with a separate nominal element-type dependency is rejected.
Empty containers retain
their unrestricted generic types. Closed naturals under the exact existing
nat-to-int mapping also qualify. The compiler checks the actual constructor and
type mappings. Global aliases, functions, applications, runtime dependencies,
custom values, callback registrations, erased or ambiguous declarations and
arbitrary constructor mappings are rejected. No recipe evaluator or recursive
runtime builder replaces the original constant expression.

Artifacts are named `soma_literal_<hash>.declaration` and
`soma_literal_<hash>.declaration-interface`. They are whole declarations, not
expression snippets. A consumer copies the entire authenticated artifact into
its receiving unit. This preserves that unit's literal-pool sharing, static
list cells, generic signatures and initialization/allocation behavior without
introducing an imported constant module or reference to another unit's pool.

Separate library metadata preserves existing descriptor layouts. Only the
owner main gains the publication identity; imported entrypoints do not inherit
it. `native_literal_declarations.manifest` authenticates the owner, Source,
selected symbol, allocated name, both declaration artifacts, complete freshly
printed ML/Mli, native identity and checked owner contract. The ordinary native
ABI report also records the identity. Generated-file ownership covers and
cleans obsolete matching declarations and manifests.

`test-suite/misc/soma_native_literal_declarations.sh` checks unchanged complete
program bytes, whole declaration and receiving-unit AST equality, reciprocal
full interfaces, generic empty lists, pairs/options/chars/escaped strings,
same-unit native string sharing and static list identity. Native and bytecode
factory/call allocations and natural Weak phases match the independent original
declaration oracle. Owner/dependency/duplicate/runtime/global rejection,
Source/product/program/ABI/contract authentication, semantic fingerprinting,
import isolation and stale-artifact cleanup cover the publication boundary.
