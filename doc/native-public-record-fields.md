# Flat public record fields

A public assembly can borrow fields of an already extracted Source record:

```soma
From Soma Require Import Native OCaml.
Record api := { api_count : nat; api_ready : bool }.
Definition bindings := Native.Export (Native.Return {| api_count := 3; api_ready := true |}).
Definition main := bindings.
OCaml Native Public Record main From bindings With
 [Field "count" := api_count; Field "ready" := api_ready].
```

This produces the complete original flat program and interface, followed by
`let count = bindings.api_count` and `let ready = bindings.api_ready`, with
signatures derived from the actual extracted field types. The native printer
supplies the allocated record labels and type names while its module visibility
context is live. No OCaml text is parsed, no projection functions are retained,
and no new initialization, record, closure, module frame or promise is added.
All original program declarations, generic helpers and record fields remain.

The receiver must be a transparent same-namespace dependency of main, with an
ordinary unparameterized runtime record type from that Source namespace. An
entry/preparation boundary is checked by its logical result type; no logical
operation to inspect executable values is introduced. Requested projections
must be the record's checked projections. Erased proof/type fields, dependent
fields, higher-rank fields, defined fields, custom/erased record representations,
wrong receivers, invalid/duplicate public names and names hiding existing
extracted values are rejected. Every selected logical projection is checked
again against its actual MiniML field position. This command does not support
parameterized records; it does not erase or narrow their public APIs to pretend
that it does.

The command adds a public producer when none exists. Declare a Public Assembly
application list before any Public Record/Public Types declarations when using
both. Multiple record selections preserve their declaration order; names must
be unique across them and applications. Type equations precede field exports.
The selected main's assembly identity includes receiver/type symbols and the
ordered field-name/position mapping. Existing metadata layouts remain unchanged;
records use a separate library object and add no identity for old producers.
Fresh whole implementation/interface, bindings, Source, layout and owner
contract hashes are authenticated by the existing native assemblies manifest.
Selections apply only to their declared main, and existing stale cleanup covers
the complete assembly products.

`test-suite/misc/soma_native_public_record.sh` compares an independent former
emitter with the new complete outputs in both directions. Native and bytecode
checks cover optional labels, retained generic helpers, single initialization,
original field/function/owner/promise identity, caller context, synchronous
faults, cancellation, exact full-unit initialization allocation and natural
Weak lifetimes. Typed rejection gates, field collisions, publication-sensitive
identity with unchanged raw programs, import/entrypoint isolation, manifest
provenance and stale artifact cleanup are also checked.
