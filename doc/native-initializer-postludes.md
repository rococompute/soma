# Nested initialization and static postludes

A checked one-time initialization can contain nested native calls:

```soma
OCaml Native Static Initialize Expression initialized : operations :=
 Call build [Value parser;Call split [Value unit_value]].
OCaml Native Reexport Binding native := initialized.
```

Unlike an `AtFullApplication` function, this expression runs at its publication
site. It accepts closed borrowed native values, checked shared data and earlier
published values/members/fields. Every call's domains, arity, residual arguments,
labels and result are checked. Callable schemas retain their actual leading
argument count, including returned function types. Partial applications retain
required/optional labels. Runtime callbacks, runtime argument indices, lambdas
and hidden initializer blueprints as leaves are rejected: each evaluated call
must appear explicitly in the expression tree.

The emitted expression is the original nested native application. It introduces
no evaluator, wrapper, prepared-input binding or reordering. Independent calls
remain independent sites; native and bytecode preserve their original sharing
and evaluation behavior. An initializer returning a tuple can be destructured
by a checked `Reexport Projection`, without rebuilding its tuple or wrapping
its members. A normal explicit call to an initializer getter evaluates its
expression; a published value reference borrows the already initialized result.

An ordinary static assembly can append ordered typed publication scopes:

```soma
OCaml Native Static Assembly main As "Checked" With [Exception "Failed" := failed].
OCaml Native Static Postlude main With
 [Modules aliases.CP;Values aliases.last;Values generic.failf;
  Types public_types.entry;Values facade.run].
```

Markers must be checked dependencies of the same Source main and match the
requested scope kind. Each selection captures its entire ordered scope, with
all typed descriptors included in the assembly's checked contract and layout
identity. Duplicate scopes, wrong owners/kinds, missing dependencies and repeated
postludes fail. The frame remains an ordinary static assembly; it cannot also
be a lexical scope. Fresh exceptions still precede Checked, and generic public
aliases remain nonexpansive aliases to their original checked functions.

The postlude is emitted directly after the checked module and its static
exports. Publication-only native wrappers for these scopes are omitted from
Checked's bindings; they may refer to Checked itself in the later publication.
They belong to that later scope rather than to runtime Source code inside
Checked. References to earlier postlude values use those same bindings. There
is no separate canonical module or dependency cycle through the facade. Native
compilation checks the whole assembly in its actual context. Other native
bindings and assemblies keep their previous emission behavior.

The new initializer operation is appended to the metadata variants. Postludes
use a separate library object and add identity only to their selected assembly.
Original descriptor tags/layouts and declarations without the new capabilities
are unchanged. All initializer leaves are logical dependencies. Explicit
`Static Invoke` functions can also borrow published values without changing
their eta boundary; their new references are retained in the logical closure.
The existing assembly manifest authenticates program, interface, bindings,
Source, layout and complete output. Captured canonical artifacts may be omitted
by a consumer only after whole-byte authentication. Existing cleanup applies.

`soma_native_initializer_postlude.sh` tests complete APIs, fresh exception
ownership, independent generic aliases, right-to-left nested initialization,
single evaluation, partial optional callables, original functions/promises/
context/faults/cancellation, exact native/bytecode allocation and natural Weak
release. Invalid types, arities, runtime expressions, scope kinds and duplicate
frames fail. Source/product authentication, assumptions, semantic/ABI sensitivity
and stale-product cleanup are checked. Existing fresh-exception, initialized
publication and lexical-environment fixtures remain regression checks.
