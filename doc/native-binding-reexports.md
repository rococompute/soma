# Borrowed native binding publications

`OCaml Native Reexport Binding name := getter.` publishes the exact checked
borrowed native value at its full declared type. Unlike `Reexport Value`, which
retains its existing callable-only restriction, `Binding` also accepts scalar,
cell, immutable-container and other closed native values. It accepts an
external value unit getter or previously checked static data; it does not call
runtime getters, read fields, evaluate effects or recover arbitrary native
expressions from strings. Checked static-invocation functions retain their
existing publication support.

A canonical unit marker records the original getter as a logical dependency.
The existing value-reexport artifacts, declaration order, Source/product hashes
and full descriptor fingerprints cover the new publications. Generic values
remain universally typed; the backend emits direct aliases with their original
public types. Mutable cells and opaque owners remain the same objects, and
closed functions remain visible as their native aliases rather than being
returned through an effect boundary. No new metadata tag, type axiom, adapter
or native evaluator is introduced. Existing `Reexport Value` declarations and
all older artifacts remain unchanged.

The binding fixture checks native and bytecode identities, generic bytes and
functions, bidirectional complete public module signatures, live cell updates,
exact returned payloads, public-call allocation, natural Weak release, Source
and product authentication, target-sensitive fingerprints, invalid declarations
and an incorrect actual OCaml scalar type. The earlier callable-value fixture
retains its original rejection of scalar `Reexport Value` declarations.

For one-time provider applications and reuse of already initialized values, see
[initialized native publications](native-initialized-publications.md).
