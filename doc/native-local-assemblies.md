# Source-owned local assemblies

A Source program can declare the public pattern for a lexical assembly:

```soma
From Soma Require Import Native OCaml.
Definition body := Native.Export (Native.Return (7, true)).
Definition main := body.
OCaml Native Assembly body As "(count, ready)".
```

Soma emits the complete `main.assembly` fragment around the fresh extracted
program, checked interface and native bindings. A build driver can insert its
bytes into the original compilation unit, retaining lexical primitive names
and native literal pooling. The driver does not supply an OCaml wrapper or
reconstruct the public declaration. `SOMA_OCAML_BINDINGS_MODULE` retains its
existing validated binding-namespace selection.

Patterns accept distinct OCaml value names, `_`, nested tuples matching the
checked product type, and complete record field puns for a declared native
record alias. Native flat triples, quadruples and quintuples retain their
arity. Partial or erased record fields, mixed or incorrect qualifications,
wrong tuple shapes, duplicate names and arbitrary expressions are rejected.
An assembly belongs to a separate transparent definition in its own Source
namespace; its already defined `main` must select that same checked value.
`main` itself is reserved for the extracted executable entry point. There is one
assembly per namespace. Its result is used once, without an extra runtime
interpreter, adapter or evaluator. Generic scalar exports retain their
polymorphism; existing static-module publication remains a separate facility.

`native_assemblies.manifest` begins with `soma-native-assemblies-v1`. Each
quoted row records the owner symbol, Source file/hash, assembly file/hash,
fresh program/interface/bindings hashes, layout identity hash and checked
owner contract. The contract is captured at the same Source checking phase as
`soma hash`, before library closure changes module-local references. The
parsed pattern participates in the semantic and native ABI identities; it
does not replace the checked body/type in the hash. Imports retain assembly
metadata, while only the selected main namespace produces its fragment.
Projects without assembly declarations retain their previous artifacts and
contracts. Producer-owned stale cleanup includes the new artifacts and
preserves edited files.

Some public functions deliberately have an eta wrapper in the original
compilation unit. They must retain that function object's identity and native
call shape rather than borrow the provider directly. A `.definition` can
request this explicitly:

```soma
OCaml Native Callable positional := string -> string.
OCaml Native External Eta Function closed : string -> string :=
  "Target.invoke" Using positional.
```

This checks the same required argument/result types and label/default schema
as `External Defaulted Function`, and emits a closed eta expression around
the typed provider. Optional defaults are omitted at full invocation; required
labels are supplied there. Native and bytecode closure sharing follows the
original OCaml expression. `External Defaulted Function` retains its existing
typed-coercion behavior for borrowing an already positional function. The
explicit eta operation has a distinct semantic/ABI identity; existing native
operation tags and descriptors are unchanged. The positional-default fixture
also checks both forms, exact promises, optional lookup phases, sharing,
provider identity distinctions and getter/public-call allocation.

`test-suite/misc/soma_native_assembly.sh` exercises native and bytecode
initialization, physical identity, literal sharing, generic inputs, native
record exports, caller context, exact promises, cancellation, synchronous and
initialization faults, exact public-call allocation, natural Weak lifetimes,
invalid patterns, semantic/ABI fingerprints and safe stale cleanup. Kykeon's
migration also compares the former assembly renderer against fresh compiler
output and runs the unchanged public assembly fixtures.

## Static module assemblies

Static publication keeps a checked module and publishes nonexpansive aliases
of its values/types, or unpacks a checked first-class module:

```soma
From Soma Require Import Native OCaml.
Definition items(A:Type) := list A.
Definition identity{A:Type}(value:items A) := value.
Definition main := @identity.
OCaml Native Static Assembly main As "Checked" With
 [Type "items" := items; Value "id" := identity].
```

`Module "Log" := body` publishes `module Log = (val Checked.body)` when
`body` has a declared packed-module representation. All references must be
transparent definitions in the current Source namespace and dependencies of
`main`, including its type annotations. Value/type/module names and kinds,
complete type constructor arities, packed-module representations, and duplicate
public names are checked. Arbitrary expressions and code-like names are
rejected. A namespace may choose either a local or static assembly.

The extractor retains the selected Source members and supplies their actual
allocated OCaml names and type parameter counts directly from its MiniML
structure and name table. Neither Python nor the Source declaration guesses
collision suffixes (a Source definition called `external`, for example, can
be emitted as `external0`). Generic value publication uses direct aliases;
there is no eta wrapper, interpreter, invocation or extra initialization.
Type aliases preserve every runtime parameter and actual compiler type
identity. The full program/interface/bindings remain in one compilation unit.

The same ten-column assembly manifest authenticates the complete fragment;
its layout identity is `native-static-assembly-v1`. The checked main contract
and native ABI include the ordered public members and Source references.
Programs without static declarations retain their extraction roots and bytes.
`test-suite/misc/soma_native_static_assembly.sh` covers unrestricted generic
values, aliases of the same closure, keyword collisions, parameterized types,
packed modules with abstract/generic/optional members, initialization order,
original mutable cells, caller context, exact promises/faults/cancellation,
allocation, natural Weak ownership, malformed declarations, semantic/ABI
fingerprints and obsolete artifact cleanup, in native and bytecode modes.

## Public implementation/interface assembly

A partial application of checked Source members can be published without a
Python implementation or signature append:

```soma
From Soma Require Import Native OCaml.
Definition prepared := Native.Export(Native.Return 3).
Definition add_using(n:nat)(value:nat) := n+value.
Definition main := (prepared,add_using).
OCaml Native Public Assembly main With
 [Apply "add" := add_using With [prepared]].
```

The declaration checks transparent same-namespace members in main's dependency
closure. Each supplied value's native representation must match its function
domain; executable boundaries erase in the compiler's type description, as
already used for native bindings. This adds no logical operation to run,
inspect or unwrap `Native.entry`. Dependent runtime argument types, wrong
arguments and duplicate/invalid/shadowing public names are rejected. The
resulting function signature is derived from its checked residual Source type.
All previous program declarations and their generic signatures remain present.

The backend uses actual allocated names and emits the complete fresh program
plus the requested applications into `.assembly`, and its complete interface
plus derived signatures into `.assembly-interface`. Applications are ordinary
native partial applications, with the same preparation, closure, invocation
and optional/default behavior as those expressions. No wrapper/interpreter or
second preparation is introduced. A final check against the actual extracted
declaration table prevents names from hiding compiler-generated or renamed
members. Both artifacts have separate rows in the existing manifest, bound to
the same fresh raw program/interface/bindings and checked owner/layout identity
`native-public-assembly-v1`. Producer-owned stale cleanup covers both outputs.

`test-suite/misc/soma_native_public_assembly.sh` compiles the actual public
implementation/interface and tests them alongside the former append expression
in native and bytecode. It exercises retained generic helpers, allocated name
collisions, single preparation, original owner/input/promise identity, caller
context, exact faults/cancellation, call allocation, natural Weak retention
and release, rejected declarations, semantic fingerprints and stale cleanup.

### Checked public type equations

Public type equations can preserve constructors and record labels without
parsing generated ML or repeating their shapes in a wrapper generator:

```soma
From Soma Require Import Native OCaml.
From Stdlib Require Import Strings.String.
Record entry := Entry { path : string; data : string }.
Definition path_of (value : entry) := path value.
Definition main := path_of.
OCaml Native Public Types main With [Type "entry" := entry].
```

The reference must be a transparent type definition or inductive type in the
same checked Source namespace and in main's dependency closure. Only runtime
type parameters are supported; indexed runtime parameters, logical parameters,
opaque types, unrelated references, non-types and invalid/duplicate names are
rejected. One declaration supplies the complete list for that namespace. If
there is also a `Public Assembly` application declaration, place it before the
`Public Types` declaration; otherwise the latter creates a public producer.

Extraction retains the referenced types and captures their representations
from MiniML while the actual OCaml printer's visibility context is live. It
uses the allocated type, constructor, field and parameter names. The emitted
equation has the form `type ... public = ... actual = ...` for ordinary
records and variants, including recursive and mutually recursive variants;
plain aliases and erased singleton representations retain their actual alias
representation. A name already equal to its actual extracted name needs no
additional declaration. A name that would hide another emitted type is
rejected; erased inline native type names do not count as emitted declarations.
Coinductive representation equations currently fail explicitly.

The complete `.assembly` and `.assembly-interface` include the equations.
They carry the existing `native-public-assembly-v1` envelope with an additional
`public-type-equations-v1` identity component. Changing only an equation's
public name changes main's checked contract. Source cannot provide arbitrary
OCaml declaration text. Existing public-application metadata is unchanged, and
clients with no type equations preserve their previous products and identities.
No runtime adapter, constructor conversion, copying or extra preparation is
introduced.

`test-suite/misc/soma_native_public_types.sh` compiles complete implementation
and interface products in native and bytecode. It covers record labels,
recursive/mutual constructors, generics, keyword type renaming, actual physical
identity and allocation, composition with partial applications, manifest/hash
agreement, rejected indices/opaque types/name collisions, semantic identity
changes and producer cleanup.

### Fresh public exception slots

A static assembly can own fresh exception constructors at its public module
boundary. For a checked native constructor such as
`OCaml Native Constructor failed : string -> exception_value := "Failed" 1`,
used by the selected Source main, declare:

```soma
OCaml Native Static Assembly main As "Checked" With
 [Exception "Failed" := failed; Value "fail" := fail].
```

The exception declarations precede the checked module, in their listed order.
The compiler emits the checked constructor payload types, then a local
`Soma_handles` inclusion and exception aliases inside the binding module. The
ordinary checked constructor/case bindings therefore use the fresh public
slots. Public exception names remain associated with the containing compiled
module, rather than with a shared helper or with `Checked`.

The constructor may be from a checked `.definition` dependency. It must be a
reachable native `Constructor` whose unqualified name matches the public name
and whose result is the standard native exception value. Nullary constructors
have no payload; ordinary constructors retain their argument representations.
Names must be distinct uppercase identifiers. Wrong constructors, unrelated
references, mismatched names, qualified external constructors, and generic or
nested polymorphic payloads are rejected. This does not introduce a logical
exception evaluator or a new assumption about native execution.

Scope metadata uses a new separate library object, preserving existing static
assembly object shapes. Its `static-exceptions-v1` component contributes to the
existing static assembly's layout and main contract. Static assemblies with no
exceptions preserve their previous identities and bytes. The complete
`.assembly` owns both the fresh slot and binding scope; a consumer copies it
without generating those declarations or rewriting binding source.

`test-suite/misc/soma_native_static_exceptions.sh` compiles complete artifacts
in native and bytecode. It checks root slot names, fresh slots in separate
modules, constructor/case agreement, declaration-before-initialization order,
nullary and multiple payloads, generic raises, original payload identity,
natural Weak retention/release, invalid declarations, semantic identity,
manifest provenance and stale producer cleanup. Retention is tested with an
actual post-GC read; the fixture does not artificially clear Weak slots or pin
payloads with GC lifetime primitives.
