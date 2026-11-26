# Owned record and exception publications

A checked native algebraic group can expose a record under a different public
name, and expose its original exception constructors alongside that record:

```soma
Import owner.
OCaml Native Reexport Record public_record := owner.node As "t".
OCaml Native Reexport Exception public_error := owner.node Constructor "Bad" As "Error".
```

`Record` accepts an owned record or an actual record member of an owned algebraic
group. Fields retain their order and mutability. Algebraic-member references,
including self references and mutually recursive sibling types, use their
canonical qualified native types. These views come from the schema type checker:
when checking a group, it prints each record's field types again with qualified
local type parameters and records that view in separate library metadata. No
reexport scans generated code or substitutes identifier text. Imported owners
without the new metadata must be recompiled. The group's previous declaration,
logical dependencies, fingerprints and serialized descriptors are unchanged.

`Exception` accepts only a checked algebraic owner and an exception declared in
that group. Its public name must be a single uppercase native constructor name.
It emits `exception Error = Canonical_owner.Bad`, preserving the original slot
for matching, raising and classification. Nullary constructors, positional
payloads and inline record payloads remain the original exceptions and original
objects; no new slot, conversion, constructor wrapper or initializer is added.
The rule cannot alias an arbitrary external exception or invent a payload type.
Fresh public exceptions in static assemblies remain a separate capability.

Record and exception publications share Source ordering, collision checks and
the complete `soma_source_types_<namespace-hash>.exports` artifact. The existing
nine-column `native_source_type_reexports.manifest` authenticates Source and
product bytes; its public-name/target columns describe the exception alias as
well as type equations. Exception markers retain their logical owner dependency.
The appended exception descriptor records its checked payload signature in its
semantic/ABI identity. Previous descriptor tags/layouts and the old declarations'
identities are unchanged. Exceptions do not become logical public type names
when printing later type aliases. Existing byte-authenticated cleanup applies.

`test-suite/misc/soma_native_owned_publications.sh` checks complete bidirectional
interfaces, renamed mutable recursive records with sibling dependencies, native
nominal identity, all three exception payload forms, catches through either
alias, original payload objects, exact allocation and natural Weak release in
native and bytecode. It rejects non-record/non-owner members, undeclared
exceptions, invalid/qualified/injected public names and duplicate publications.
It also checks assumptions, Source/product hashes, exception-signature-sensitive
semantic/ABI fingerprints and obsolete-product cleanup. The existing Source
record/variant/group publication fixture continues to pass unchanged.
