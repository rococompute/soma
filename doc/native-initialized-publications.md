# Initialized native publications

A checked native publication can apply a provider during module initialization,
then borrow that same published result in subsequent declarations:

```soma
OCaml Native Static Initialize initialized : owner_type := make_owner With [seed].
OCaml Native Reexport Binding owner := initialized.
OCaml Native Published Value shared_owner : owner_type := owner.
OCaml Native Static Initialize prepared : public_call := prepare With [shared_owner].
OCaml Native Reexport Binding run := prepared.
```

`Initialize` checks unit-getter inputs, a nonempty supplied prefix, every native
domain, the residual result and its labels. A complete application may produce
a scalar, record or callable schema; a partial application retains its remaining
arguments. Inputs borrow declared native external values, checked shared static
data or earlier publications. Runtime field reads, dynamic callbacks, nested
initializer blueprints and inline literal blueprints are rejected. Stage a
literal as owned shared data rather than inventing another literal object at
the initialization site. Leading type parameters follow the existing native
checker rules; full generic aliases and covariant initialized factories retain
their public types, subject to actual OCaml value restriction checking.

`Published Value` names an earlier `Reexport Binding` or callable value marker.
Its declared logical type must convert to the original checked getter's result,
including type parameters. The canonical marker is a logical dependency of the
new getter; no logical operation inspects a native value. Initializers likewise
record all original getter dependencies. Descriptor/result/label/reference
changes participate in the semantic and ABI fingerprints. New operation cases
are appended; old tags and layouts are unchanged.

These are global native publications. A participating namespace is emitted once
as `soma_published_<namespace-hash>.ml`, with its declarations in their checked
order and full type annotations. The raw export artifact includes that module;
the native binding namespace aliases it. Normal published-value getters and
references from another namespace therefore reuse the same initialized objects
and functions. Neither path runs a second initializer. Within its owner module,
a reference uses the original earlier binding directly. Elsewhere it names the
canonical module. Ordinary initialization expressions remain direct native
applications: no effect export, evaluator, tuple bridge or adapter hides the
native function or redoes its preparation. Calling an initializer getter itself
explicitly evaluates its application; borrowing a publication does not.

`native_binding_initializers.manifest` starts with
`soma-native-binding-initializers-v1`. Each quoted row records namespace, Source
path/hash and canonical module filename/hash. The existing value-reexport
manifest authenticates the complete export artifacts. Producer-owned cleanup
includes canonical modules and the new manifest, with the existing byte-match
requirement before deletion. A project with no new initialization/reference
operations retains its previous files and identities.

The fixture `soma_native_initialized_binding.sh` checks ordered initialization
with effectful producers, one owner across raw exports/getters/namespaces,
original cells/functions/payloads, labels, independent generic instantiations,
caller context, original promises/faults/cancellation, exact native/bytecode
allocation and natural Weak release. It rejects invalid references, generic
mismatches, wrong types/arities, dynamic and literal blueprints, authenticates
Source/product bytes, checks semantic/ABI sensitivity, and removes obsolete
products. Existing callable and borrowed-binding publication fixtures pass
unchanged.
