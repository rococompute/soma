# Checked canonical schema includes

A Source main may publish the complete canonical native algebraic schema in
place of one extracted member alias:

```soma
OCaml Native Canonical Include main From primitives.t.
```

The selected owner must be the transparent `main` of the declaring Source.
The member must be a checked dependency of that main and belong to a native
algebraic schema containing only types. The declaration does not accept OCaml
text, arbitrary module paths, runtime initializers or exception declarations.
Duplicate includes of a schema are rejected.

The real OCaml printer observes the original member alias in both the complete
implementation and interface. Its allocated name must equal the canonical
member name and have no parameters. The alias is suppressed; the compiler
prefixes the whole implementation with `include Canonical` and the whole
interface with `include module type of struct include Canonical end`, deriving
the owner from the checked schema. Every original value, helper, brand,
unrestricted generic signature and runtime initializer remains unchanged.
Putting the include before the whole program preserves the existing order of
constructor and record-label visibility. Other extracted types or another
include may not collide with any member of the complete published schema.

Separate library metadata leaves existing descriptor layouts unchanged. Only
the declaring main gains a semantic identity containing the member, canonical
owner and digest of the complete schema. Imported entrypoints do not inherit
that main's publication. `native_canonical_includes.manifest` authenticates the
Source, member, canonical owner, complete schema artifact, full ML/Mli and ABI
identity. The generated-file registry removes obsolete matching manifests.

`test-suite/misc/soma_native_canonical_includes.sh` compares the complete former
Kykeon include/alias replacement against the compiler outputs, without dropping
or normalizing any AST nodes. It exercises reciprocal full interfaces,
canonical record/variant identity, generic functions, live mutation, promise
and function identity, caller context, synchronous faults, cancellation, exact
initialization/call allocation and natural Weak retention/release in native
and bytecode. Rejection, provenance, owner hashing, import isolation and stale
metadata checks cover the publication boundary.
