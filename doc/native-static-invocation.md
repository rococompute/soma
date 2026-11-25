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
