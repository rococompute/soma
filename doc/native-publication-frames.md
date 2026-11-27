# Borrowed publication scopes and binding operators

A Source main can enclose a complete checked borrowed-value scope and publish
binding-operator aliases to its members:

```soma
OCaml Native Publication Frame main From bind As "Checked_bind"
 With [Operator "let*" := bind].
```

The marker is a checked dependency of this Source main and selects its entire
ordered native value-publication scope. Every member must be a borrowed external
value alias; evaluated initializers and projection scopes are rejected. The
module contains all original declarations, with their full explicit polymorphic
annotations. Operators are direct aliases to the original member values, with
signatures derived by the existing native binding checker. No function wrapper,
conversion, evaluator, preparation, record copy or new exception is added.

The frame wraps only the value scope. It does not enclose the ordinary extracted
program or introduce its brands/helpers into that scope. Generic identity,
return and bind values therefore retain their original function objects and
unrestricted type variables. The complete module API is retained alongside the
operator aliases. The ordinary program and ordinary private scope bindings are
still emitted unchanged; consumers can copy the complete Source-owned assembly.

Module identifiers and binding-operator identifiers are validated, and each
operator must select a member of this scope. Wrong owners/dependencies/kinds,
missing/repeated/out-of-order scopes, duplicate operators, invalid/reserved
names and mixed public-assembly declarations fail. The frame creates its own
public producer. Its separate library object leaves old descriptor layouts
unchanged. Only the selected main gains a frame identity; the scope marker and
its original proof fingerprints remain unchanged. The identity captures the
module name, operators and ordered full-scope descriptor digests, checked again
against the actual native module table before output.

The existing native assembly manifest authenticates Source, fresh whole program,
interface and bindings, owner contract, layout and complete frame ML/Mli.
Importing a framed source does not frame another entrypoint; producer-owned
obsolete-artifact cleanup applies.

`test-suite/misc/soma_native_publication_frames.sh` compares an independent old
scope wrapper with the new complete implementation byte-for-byte. Native and
bytecode reciprocal full APIs, unrestricted generics, original operator/function
identity, promises/context/faults/cancellation, exact initialization/call allocation
and natural Weak lifetimes pass. Typed rejection gates, original marker proof
fingerprints, Source/product evidence, name-sensitive main identity with unchanged
raw programs, imported entrypoint isolation and stale cleanup are checked.
