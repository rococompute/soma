# Checked record views for native external aliases

A Source main can expose a checked record representation at an existing opaque
native type alias, without changing any Source value or extracted operation:

```soma
OCaml Native Record View main Replace primitives.item With publications.checked.
```

`publications.checked` is an existing typed `Reexport Source` or `Reexport
Record` declaration with a complete monomorphic record body. The original must
be a monomorphic native external type alias reachable through the selected
transparent Source main. Its native target must exactly equal the publication's
nominal target. Wrong owners, unrelated aliases, non-type/native-family operands,
non-record or parameterized publications, mismatched targets and duplicate views
are rejected. The ordinary native compiler checks the complete record equation
against its actual native owner's fields, order, types and mutability.

The OCaml printer changes only the original alias declaration, in place, in
both the complete implementation and interface. It derives the full shape from
checked publication metadata and uses the real printer-allocated type name,
regardless of the publication marker's requested name. All original type
references, helpers, generic signatures, value printers, brands, record objects,
callbacks, promises, initialization and ownership boundaries remain unchanged.
No logical executable-value eliminator, converter, record copy, wrapper or
runtime operation is introduced. Inline/erased aliases or missing/differing
implementation/interface declarations fail rather than silently dropping a view.

Separate library metadata preserves existing descriptor/object layouts. Only
the selected main gains the view identity, which includes original/publication
symbols and a digest of the complete checked representation. Imported entrypoints
do not apply another main's views. `native_record_views.manifest` authenticates
Source, original/marker/target/allocated name, whole fresh ML/Mli and the native
ABI identity. Fresh extraction must observe the same name in both outputs.
The existing project ownership registry includes and cleans this manifest.

`test-suite/misc/soma_native_extraction_record_views.sh` compares the complete
former alias-rewrite algorithm with the new full program in native and bytecode.
It checks full reciprocal interfaces, original nominal record fields, retained
generics, owner/field/function/promise identity, caller context, synchronous
faults, cancellation, exact unit/call allocation and natural Weak ownership.
Typed rejection gates, actual native record-shape mismatch rejection, Source/
product/ABI authentication, import scoping and obsolete metadata cleanup pass.
Existing imported-type-equation and public-record fixtures remain regressions.
