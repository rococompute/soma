# Native algebraic reexports

Publish an existing owned native type group under an existing provider's type
equations without converting values or copying provider helpers:

```soma
From Soma Require Import Native.
Import storage.
OCaml Native Reexport Algebraic api := storage.node As "Target.Storage".
```

The source must name a member of an already checked native algebraic group.
The complete group is reexported, preserving recursion, constructor order and
arity, inline records, field names/types and mutability. The target is a valid
uppercase dotted module path. Duplicate exported type names within a Source
scope are rejected. Other native/logical type shapes require their own typed
support; this declaration does not accept an arbitrary OCaml schema string.

The compiler emits equations such as `type node = Target.Storage.node = ...`.
It also emits a type-only empty-signature witness requiring the target's actual
nominal types to equal the owned schema's types. A same-shaped but unrelated
nominal target is rejected by native compilation. The witness adds no public
helpers or values, and schema exceptions are deliberately not reexported.
There is no value converter, native evaluator or new axiom. The declaration's
logical unit marker retains its checked owner dependency and canonical body.

Standalone bindings provide one `Soma_types_<namespace hash>` module per scope
with complete alias interfaces. `.exports` artifacts contain the exact type
witnesses/equations for lexical embedding. `native_algebraic_reexports.manifest`
authenticates the source symbol/namespace/file/digest, artifact/digest, owner,
target and declaration order. The schema, target and ownership participate in
ABI and semantic fingerprints. Existing algebraic schema rendering remains
byte-for-byte unchanged when no reexport is requested.

`test-suite/misc/soma_native_algebraic_reexport.sh` checks native and bytecode
recursive and single-record aliases against the actual target and owned
schema. It covers constructors, inline records, mutable fields, borrowed
buffers/tables/children, exact allocation, canonical markers and changed target
fingerprints. It rejects duplicate names, unsupported schema owners, code-like
targets, extra exception access and a structurally identical unrelated nominal
target. The nominal witness is emitted for both native implementations and
interfaces; no assertion is deferred to a runtime adapter.
