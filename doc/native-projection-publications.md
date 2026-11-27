# Native tuple publications

A Source declaration can publish the members of an existing native tuple and
borrow an individual member for a later checked initialization:

```soma
OCaml Native External Value commands_value : command_tuple := "Provider.commands".
OCaml Native Reexport Projection commands := commands_value As "(read, (write, _))".
OCaml Native Projected Value write_value : owner -> string -> unit :=
  commands Member "write".
OCaml Native Static Initialize prepared : public_call := prepare With [write_value].
OCaml Native Reexport Binding run := prepared.
```

`command_tuple` describes the complete actual tuple, including ignored members.
The existing checked structural-pattern parser verifies names and nested binary,
triple, quadruple or quintuple tuple shapes. Complete checked record patterns are also supported; see
[record publications](native-record-publications.md). Arbitrary native
expressions are rejected. Duplicate public
names are rejected across both projections and ordinary binding publications.

The input must be a positional unit getter borrowing a native value, checked
shared static data or an earlier published value/member. Runtime callbacks and
initializer blueprints are rejected. A projected member's declared result must
unify with its actual logical component type. Leading generic parameters of the
original tuple are instantiated independently, so a monomorphic member need not
carry unrelated phantom parameters; generic members retain their full public
types. The normal OCaml compiler also checks the emitted tuple annotation.

A projection emits one direct `let pattern = (original_value : tuple_type)` in
the namespace's canonical `soma_published_<namespace-hash>.ml`, in declaration
order alongside ordinary publications. No tuple is rebuilt and no component is
wrapped. Native bindings, raw exports and later initialized publications use the
same original functions, cells and objects. Even a namespace containing only
projections has a canonical module and a raw export artifact. A mutable native
field is read once there: raw exports do not take a second snapshot when loaded
later. Explicit native input-getter calls keep their original behavior.

The projection marker depends logically on the original getter; a projected
getter depends on its marker. Structured pattern, signatures, native descriptor,
namespace, owner and declaration order participate in semantic/ABI identity.
The new operation and metadata constructors are appended without changing the
previous constructors' tags or layouts. Existing publication products and
identities remain unchanged when projections are absent.

`native_binding_projections.manifest` starts with
`soma-native-binding-projections-v1`. Its nine quoted fields are marker symbol,
namespace, Source path/hash, complete raw artifact filename/hash, comma-separated
member names, original getter symbol and declaration ordinal. Ordinals share the
sequence used by ordinary value publications. The existing initializer manifest
authenticates canonical modules. Producer-owned cleanup removes obsolete
manifests, modules and raw artifacts only when their prior recorded bytes match.

`test-suite/misc/soma_native_projection_publication.sh` checks complete interfaces,
independent generic members, projection-only namespaces, mixed declaration order,
a mutation between binding and raw-export initialization, exact function/cell/
payload identities, promises/context/faults/cancellation, native/bytecode allocation
and natural Weak release. Invalid members, types, patterns, owners, collisions
and dynamic getters fail. Source/product authentication, trusted assumptions,
semantic/ABI sensitivity and stale-product cleanup are checked as well.
