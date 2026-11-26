# Direct native field values

A definition can borrow a field of a module's existing record value:

```soma
OCaml Native External Field Value storage : storage_ops :=
  "Guest_public_runtime.commands.storage_provider".
OCaml Native Reexport Binding public_storage := storage.
```

The grammar requires one or more uppercase module identifiers followed by a
lowercase value identifier and at least one lowercase field identifier. Nested
field chains are supported. Empty components, keywords, wildcards, calls,
operators, injected expressions and module components after the record value
are rejected. Ordinary `External Value` keeps its original module/value-only
grammar. The new declaration uses the existing external-constant descriptor;
no metadata tag, axiom or logical evaluator is introduced. The complete checked
path remains in semantic and ABI fingerprints.

The generated getter directly selects that field at its declared native type.
Actual OCaml compilation verifies field existence and the complete field type,
including polymorphic functions. No adapter, reconstruction, object copy or
per-call closure wraps the field. Calling a unit getter reads the current field;
publishing it through `Reexport Binding` reads it once at publication time.

Field-publication namespaces use the canonical initialized-publication module.
Raw exports and native binding namespaces share that same module, even when the
namespace has no other initializer. A later mutation between module
initializations cannot make two publications take different snapshots. The
existing initialized-publication manifest authenticates the canonical complete
bytes. Programs without field publications retain their former output and
fingerprints.

`soma_native_external_field_value.sh` checks scalar/owner/cell/string and
polymorphic record fields, full bidirectional public signatures, exact provider
and function identities, generic bytes/functions, promises/payloads, exact call
allocation and natural Weak release in native and bytecode. A separate module
mutates the record after the canonical/binding module initializes but before the
raw export module: both publications must still hold the first cell. A direct
unit getter must instead observe a later replacement. Invalid grammar and
incorrect actual native field types fail; changed field paths alter both hash
families. Existing initialized-publication behavior remains covered separately.
