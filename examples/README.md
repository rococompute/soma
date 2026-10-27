# Examples

Small Lightlang programs. Run one with:

```sh
_build/install/default/bin/rocq c examples/hello.light
```

- `hello.light`: hello world.
- `string_formatting.light`: building strings with Stdlib's `append` and
  `DecimalString`, with a parameter whose type is inferred.

Outside a proof, a bare term such as `greet "world".` is evaluated and printed,
like `Eval lazy in greet "world".` Other strategies are still available:
`Eval cbv in ...`, `Compute ...` (the VM, which falls back to `cbv` under
`Gradual Typing`), and `Eval simpl in ...`, which only rewrites the term for
readability.
