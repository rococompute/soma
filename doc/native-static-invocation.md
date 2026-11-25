# Typed static invocation

A native function can derive several arguments from the same public input
without capturing getter results in a new closure. Declare each borrowed leaf
as an `OCaml Native External Value`, then describe a checked application tree:

```soma
OCaml Native Static Invoke prepared : public_call := target With
 [Argument 1; Argument 0; Call reader [Argument 1]] AtFullApplication.
```

`Argument` uses a zero-based public parameter index, `Value` borrows a declared
closed native value/function blueprint, and `Call` applies a declared blueprint
to another nonempty argument list. The checker verifies every index, argument
domain and result, including public callable labels, optional arguments and
leading generic type parameters. Ordinary borrowed arrows may be partially
applied to return a checked function value. A partially applied labelled result
requires an explicit callable return schema. Dynamic native callbacks and
arbitrary OCaml expression strings are rejected.

The backend emits one closed function literal with the original direct calls
inside its fully applied body. Repeated inputs, derived callback creation,
literals, native argument evaluation order and tail calls retain their native
scope. The getter does not run the application tree during initialization or
partial application. There is no per-call interpreter, tuple bridge, logical
native evaluator, new axiom or handwritten policy adapter.

The new operation is appended to native metadata and fingerprints its checked
application tree and labels. Older descriptor encodings and rendering remain
unchanged. A cold comparison with the preceding compiler reproduces all 22
older fixture products and its complete Source contract/witness hash report
byte-for-byte.

`test-suite/misc/soma_native_static_invocation.sh` checks native and bytecode
closed sharing, live/repeated inputs, right-to-left failure prefixes and exact
exceptions, optional defaults/labels, generic bytes/functions, independently
widened rows, constructors/literal identities, exact promises/Lwt context and
cancellation, quiet partials, exact allocation and natural Weak owner lifetimes
(including collection inside the target tail continuation). It also rejects
invalid indices, domains, results, arities, dynamic callbacks and an invalid
higher-order native boundary; changing argument order changes ABI and semantic
hashes. All six existing static application/scope/function, open variant,
closed factory and full field/literal regression suites pass unchanged.

Over 10,000 calls, before/after allocation is exactly 4,160,096 bytes natively
and 4,080,144 bytes in bytecode; wrapper creation is 96 / 240,144 bytes in the
respective backends.

## Nested callable scopes

An argument tree can contain a typed function literal:

```soma
OCaml Native Callable continuation := prepared -> status.
OCaml Native Static Invoke entry : owner -> source -> status := prepare With
 [Argument 1; Function continuation [Call resume [Argument 0; Argument 2]]]
 AtFullApplication.
```

`Function` names a declared native callable schema. Its parameters are appended
to the enclosing argument context, so the example's `Argument 2` is the
continuation parameter while `Argument 0` retains the original owner. Nested
and sibling functions have separate lexical scopes. Out-of-scope indices,
non-callable schemas and wrong callback results are rejected. Leading generic
parameters, required labels and optional parameters follow the callable schema.
Both the callback body and its complete instantiated signature participate in
ABI and semantic fingerprints, even when an argument is unused.

The backend emits the native function literal directly at its original
creation site. Captured owners, callback arity, delayed execution, tail-call
frames and closed-function sharing retain the native behavior without a
callback interpreter or tuple conversion. Use callable schemas explicitly for
labelled native higher-order function arguments.

`OCaml Native Assertion Function invalid : input -> answer := line column.`
provides a typed closed function which raises the original assertion with
`__FILE__` and the declared location. Unlike a factory, its getter returns the
actual assertion callback. Static invocation can embed it as a function value
or call it while preserving evaluation of the ignored argument. Invalid
locations, multiple arguments and labelled inputs are rejected.

`test-suite/misc/soma_native_static_lambda.sh` compares nested captures, live
owners, generic bytes/functions, labels/optional callbacks, quiet partials,
exact assertion locations, exceptions, promises/context/cancellation, exact
allocation, and natural Weak lifetimes including a consumed owner inside a
target tail continuation. It rejects scope escapes and checks fingerprint
changes for both capture order and an unused callback argument's type.
