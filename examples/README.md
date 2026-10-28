# Examples

Small Lightlang programs. Run one with:

```sh
_build/install/default/bin/rocq c examples/hello.light
```

- `hello.light`: hello world.
- `string_formatting.light`: `to_string` on strings, numbers and lists, and
  a `greet` that accepts any of them.
- `compile_time_vs_run_time_error.light`: a wrong argument is rejected when
  the program is checked, unless the parameter is `Any`; then it fails with
  `raise` when it runs.
- `basic_fibonacci.light`: the textbook recursive `fib`, with `Recursive`
  and `match`.
- `gradual_fibonacci.light`: a linear-time `fib`, first with its types
  inferred as `nat`, then with them written as Stdlib's binary `N` for large
  results.
- `recursive_countdown.light`: why a recursive call on `n - 1` is rejected,
  and the `Succ m` countdown that is accepted.
- `sqrt2_irrational.light`: a proof that the square root of 2 is irrational
  (`irrational (sqrt 2)`), top down: the theorem first, then a proof that
  reduces it with `enough` to the rationals, to whole numbers, and to
  "`n * n` even means `n` even". `lia`, `nia` and `lra` do the arithmetic.
- `sqrt2_irrational_bottom_up.light`: the same proof bottom up, as separate
  named lemmas proved before the theorem that uses them.

Outside a proof, `Definition` can be left out: `greet name := ...` is
`Definition greet name := ...`. Recursive functions still need `Recursive`.

Outside a proof, a bare term such as `greet "world".` is evaluated and printed,
like `Eval lazy in greet "world".` Other strategies are still available:
`Eval cbv in ...`, `Compute ...` (the VM, which falls back to `cbv` under
`Gradual Typing`), and `Eval simpl in ...`, which only rewrites the term for
readability.
