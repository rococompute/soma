# Checked native record publications

A native projection may destructure a complete existing checked record:

```soma
OCaml Native Record Alias state := producer.state As "Provider.state".
OCaml Native External Value original : state := "Provider.live".
OCaml Native Reexport Projection members := original As
 "{ Provider.counter; run; ready }".
OCaml Native Projected Value run_value : string -> promise buffer :=
 members Member "run".
```

This uses the existing structural record pattern, native record alias and
publication machinery. The full field set must match the original Source
record; the qualification must match its checked native alias. Constructor type
parameters are instantiated with the receiver's actual arguments, then each
field's logical type is inferred in the listed pattern order. Projected members
are checked against those types independently, preserving unrelated generic
parameters and ordinary required/optional callable labels.

The original native record alias checks still reject type-valued, proof,
dependent or polymorphic fields and unsupported record shapes. Partial field
sets, extra/duplicate names, mismatched owners, arbitrary native expressions,
wrong member types, dynamic getters and publication-name collisions fail.

Emission is a single directly typed `let { Provider.field; ... } = value`, at
the original publication position. The value may be borrowed or the result of
an explicit checked nested initializer. There is no reconstructed record,
extra public owner binding, field wrapper or conversion. In particular,
retaining one resulting function does not keep the discarded record or its
other fields alive. Compiler-owned canonical and raw artifacts retain their
existing publication snapshot behavior.

Record pattern, owner, field types and declaration order enter the existing
semantic/ABI identities and manifests; no metadata constructor or layout is
changed. Existing tuple publications and record assemblies retain their output.
Producer-owned cleanup and Source/product authentication apply as before.

`test-suite/misc/soma_native_record_publication.sh` checks complete public APIs,
independent generic member inference, single initialization, original cells and
functions, promises/context/faults/cancellation, exact native/bytecode call and
initialization allocation, and natural separate-member Weak lifetimes. It also
checks invalid declarations, artifact provenance, record-order identity
sensitivity and stale publication cleanup. Existing tuple-projection and record
assembly fixtures provide compatibility checks.
