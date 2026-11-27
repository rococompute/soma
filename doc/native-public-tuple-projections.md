# Flat public tuple projections

A Source main can publish members of an existing extracted tuple:

```soma
OCaml Native Public Projection main From fields As "(octal, cstr, pax)".
```

This emits the complete original flat implementation/interface, followed by a
single direct destructuring binding and checked member signatures. It uses the
real extracted receiver name. The receiver is not re-evaluated, copied or wrapped;
all original helpers, generic APIs and runtime declarations remain present.
Nested pairs and native triples/quadruples/quintuples preserve their checked
structure. Underscores skip existing members without replacing the tuple.

The owner must be the transparent main in its Source namespace; the receiver
must be its transparent checked dependency. The existing export-pattern checker
checks structure, arity, identifier syntax and distinct names. Each leaf,
including skipped members, must have a monomorphic runtime representation:
erased proof/type fields and hidden higher-rank fields are rejected. Record
patterns use the separate public-record capability. Public names cannot hide
actual extracted values or other application/record/projection exports. Argument
labels and member signatures come from the checked logical type using the same
native representations as existing bindings. No logical operation to inspect or
eliminate an executable boundary is added.

Public Assembly applications, when used, precede Projection/Record/Types/Modules
declarations. Projection creates a public producer if none exists, and multiple
projections retain Source order. It adds no main tuple, closure, evaluator,
Checked frame, preparation, constructor or promise. Separate library metadata
leaves previous object layouts unchanged; old producers gain no identity. The
selected main's assembly identity includes receiver symbol, structural pattern
and full member signatures. The existing complete assembly manifest authenticates
Source, program/interface/bindings, layout, owner contract and complete outputs.
Imported entrypoints do not publish another owner's projections; stale cleanup
follows the existing producer ownership registry.

`test-suite/misc/soma_native_public_projections.sh` compares complete native and
bytecode units with an independent original emitter. It checks reciprocal APIs,
flat/nested tuple shapes, generic helpers, original members/owner/function/
promise identity, optional labels, caller context, exact faults/cancellation,
exact full-unit/call allocation and natural Weak retention/release. Wrong
owners/dependencies/arity/patterns/names, colliding extracted helpers and erased
or polymorphic skipped fields fail. Source/product evidence, name-sensitive
identity with unchanged raw programs, import scoping and stale cleanup pass.
