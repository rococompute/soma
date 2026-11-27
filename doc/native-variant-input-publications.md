# Checked upper-row function publications

A public function can retain an upper-bounded polymorphic-variant input while
borrowing its existing closed-row implementation:

```soma
OCaml Native External Value original : mode -> string -> string := "Target.call".
OCaml Native Reexport Variant Input apply := original At 0
 Parameters ["mode";"text"].
```

The Source `mode` must be a checked closed native polymorphic variant. Soma
emits an ordinary nonrecursive function whose selected parameter has the
`[< ...]` row derived from that same variant's tags and payload types, and
coerces it directly to the closed implementation type before the original call.
Other arguments and the result retain their checked native types. No tag/payload
reconstruction, match, callback/effect bridge, conversion function or per-call
allocation is introduced. The original closure, values, promise, exceptions,
caller context and ownership remain observable at the same points.

This declaration is publication metadata, like other native reexports; its
Source marker is unit and depends on the original checked getter. The getter
must borrow a monomorphic native function with positional, nondependent arrows.
The selected argument must be a closed native variant. The position and full
parameter list must match the function. Duplicate names, wildcards, keywords,
malformed identifiers, target-shadowing parameters, labelled/dependent/generic
functions, open/opaque domains and dynamic callbacks are rejected. This does
not add a general Source row type or grant exhaustive matching on an open row.

A separate persistent library object stores the checked position, parameter
names, domains, result and original variant descriptor. This metadata extends
only its publication's semantic identity and ABI description. Existing native
operation tags, records, manifests and publications without this rule retain
their prior representation and output. Complete value artifacts use the normal
publication manifests, scope order/collision checks, byte authentication and
producer-owned cleanup.

`soma_native_variant_input.sh` checks the full inferred API in both directions,
row subtypes and payload types, physical row/payload/promise identity, context,
synchronous faults, cancellation, exact native/bytecode allocation and natural
Weak ownership of a partially applied variant payload. It also checks invalid
positions/shapes/domains/parameters, no new assumptions, Source/product/ABI
identity, selected-position hash sensitivity and obsolete-product cleanup.
