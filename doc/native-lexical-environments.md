# Checked lexical environments

A lexical assembly can declare its surrounding typed publications and module
applications without supplying native wrapper text:

```soma
OCaml Native Static Assembly main As "Checked" With [Value "start" := start].
OCaml Native Lexical Scope main Open ["Platform"]
 Functor "Main" With ["B":"Platform.Block";"S":"Platform.Stack"].
OCaml Native Lexical Environment main
 Prefix [Values publication.last;Modules aliases.Network]
 Modules [Module "N" := "Network" Apply ["S"]]
 Local [Module "Setup" := "Platform.Setup" Apply ["B"]].
```

Each prefix selects an entire existing checked publication scope. `Values`,
`Modules` and `Types` accept the corresponding native publication markers,
which must contribute to the checked main's Source dependency closure. Every
member of the captured scope is recorded in its checked layout, including members
not referenced separately by main. Prefix scopes retain declaration order; duplicate scope selections and wrong marker
kinds fail. Module names, paths and arguments are validated identifiers, never
native expressions. Duplicate/reserved module names, functor-parameter shadowing
and malformed paths fail. An alias omits `Apply`; applications preserve their
listed argument order. Final native compilation checks the actual functor
signatures and abstract type relationships.

The compiler emits opens, prefix scopes, the optional public functor, its body
modules and its lexical value binding in that order. Local modules precede the
sealed checked module inside the value expression. A local functor is therefore
applied at the original binding's initialization point, rather than globally or
once per call. Original generative exception slots, initialization faults and
private module ownership remain observable at the same points.

Prefix value scopes are emitted directly, with their full checked annotations,
in the enclosing scope. Their native binding references use those same earlier
bindings. No separate canonical module is required, no initializer is repeated
and no extra module object retains the complete prefix environment. Ordinary
publications outside such a lexical environment retain their canonical-module
behavior. This also permits outer platform providers that depend on a core
library without introducing a dependency cycle through that library.

A published record can supply a field to later initialization:

```soma
OCaml Native Get select_broker : settings -> (unit -> string) := "broker".
OCaml Native Static Project broker : unit -> string := select_broker From public_settings.
```

`public_settings` is an earlier `Reexport Binding` marker. The selector must be
a checked positional `Native Get`, its receiver must convert to the original
published owner's logical type, and its result must convert to the new getter's
result. The compiler emits a direct, explicitly typed field read from that
published object. It neither calls a wrapper selector nor rebuilds the record.
The getter retains logical dependencies on the selector and publication; its
field/result are also checked by native compilation. Initialized publications
can borrow the projected field as an input or function, preserving argument
labels and ordinary native evaluation order.

The environment is separate library metadata, included in the assembly's checked
contract and layout identity. The new projection operation is appended, preserving
old descriptor tags/layouts and existing clients' fingerprints and output. The
existing assembly manifest authenticates Source, program, interface, bindings,
layout and complete output; existing producer-owned cleanup applies. Consumers
can omit separately emitted prefix modules only after authenticating their full
capture in the assembly, as with captured owned callables.

`soma_native_lexical_environment.sh` checks the full public module API, original
field snapshot, initialization order, generative slots, promises, caller context,
faults/cancellation, exact native/bytecode call allocation and natural local
functor Weak ownership. Invalid dependencies, selector/owner/result types,
publication kinds, names and modules fail. Source/product authentication, trusted
assumptions, semantic/ABI sensitivity and obsolete assembly cleanup are checked.
The existing lexical-scope fixture passes unchanged, including its frozen
allocation and Weak observations.
