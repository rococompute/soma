# Checked static applications

A static assembly may publish applications of its own checked Source functions:

```coq
OCaml Native Static Assembly main As "Checked"
 Applications [Apply "parse" := unwrap With [parser_value]]
 With [Exception "Bad" := make_bad].
OCaml Native Lexical Scope main.
```

`unwrap` must be a transparent constant belonging to the current Source module
and a dependency of `main`. Each argument names a referenced, monomorphic,
positional native unit getter that borrows an already available value. Dynamic
callbacks, arbitrary expressions and native calls are rejected. Leading type
parameters of the function are inferred by unification against those checked
input types. Runtime dependent results, excess arguments, unresolved generic
results and duplicate public names are rejected. The resulting public type must
be monomorphic and supported by the OCaml backend.

In a lexical exception scope the private binding record includes only native
callbacks referenced by the extracted runtime. Foreign modules selected only
for an application argument type do not add unused callback closures to it.

The applications use the function's fresh extraction name inside `Checked`.
In a lexical assembly they occur directly in the existing result tuple outside
the sealed module, at the declared positions. They introduce no new wrapper,
helper binding, callback bridge or conversion. This retains the original OCaml
evaluation order and lets the private function keep its unrestricted generic
interface. Ordinary static assemblies emit equivalent direct public `let`
bindings. A zero-input application can select a monomorphic Source value in the
same declaration.

All argument descriptors and the inferred public signature contribute to the
assembly ABI/layout identity. The complete emitted assembly is authenticated
along with its Source, private program/interface and native bindings. Extraction
without the declaration removes stale output. Existing static assemblies do
not change their descriptor representation or identity.

Static exception scopes also accept an existing nullary External Exception
whose checked public path matches the fresh slot name. The original native
getter is rebased to that enclosing slot, just as for constructor descriptors.
This does not equate two independently declared exception slots.

`test-suite/misc/soma_native_lexical_application.sh` checks two different
instantiations of a generic function, complete APIs, original initialization,
promise/result/context/exception/cancellation behavior, exact allocation and
natural independent Weak lifetimes in native and bytecode. It checks rejected
shapes, authenticated artifacts, ABI input sensitivity and stale output cleanup.
