# Flat aliases for canonical native layout modules

A Source main can publish the complete module owning a native schema type:

```soma
OCaml Native Public Modules main With
 [Module "Layout" := native_storage.node;
  Module "Settings" := native_storage.settings].
```

The selected reference must be a checked dependency of that transparent Source
main and a native owned record, immutable record or algebraic schema type.
The compiler derives its canonical module from the typed descriptor. Source
never supplies a generated module hash or OCaml declaration text. Selecting any
member of an algebraic group aliases its whole canonical module, preserving all
mutually recursive types, record labels/mutability, constructors, exceptions and
other public declarations. The canonical owner must be among the selected
native products. External opaque types, unrelated or non-schema dependencies,
wrong owners, invalid/duplicate/reserved names and module-name collisions fail.

This creates a public assembly when none exists. Declare Public Assembly
applications before Public Modules/Public Record/Public Types when combining
them. Only one ordered Public Modules list belongs to each main. The native
producer emits direct `module Layout = Soma_...` aliases before the full fresh
program and its full interface. It adds no module frame, record copy, fresh
exception, callback wrapper, additional initialization or runtime interpreter.
The complete original unit, including generic helpers and brands, is preserved.
The original schema files are emitted unchanged and remain the canonical
owners. The public module aliases have the same nominal equalities in ML/Mli.

The producer validates each selected descriptor and canonical owner again
against its native module table. Module names come from the real printer's
fresh declaration context. Separate library metadata preserves existing object
layouts; old producers receive no new identity. The selected main's public
assembly identity captures public names, schema references, canonical targets
and digests of complete native schema identities. Digests keep nested schema
text out of the manifest's identifier-only layout envelope. The existing
assembly manifest authenticates fresh whole program/interface/bindings, Source,
layout, owner contract and complete emitted assembly bytes. Entry-point scoping
and producer-owned stale cleanup apply as for other public assemblies.

`test-suite/misc/soma_native_public_modules.sh` compares the complete old
canonical-alias emitter with the new compiler output in native and bytecode.
It checks full signatures in both directions, mutually recursive constructors,
record mutation and nominal identity, original exceptions and immutable record
getters, retained generics, single initialization, exact whole-unit allocation,
original initialization faults and natural Weak lifetimes. Typed rejection
gates, whole artifact provenance, name-sensitive identity with unchanged raw
programs/canonical owners, import isolation and stale cleanup are covered.
