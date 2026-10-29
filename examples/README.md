# Examples

Small Soma programs. Run one with `soma run` (in
`_build/install/default/bin` once Soma is built), which prints the value
of its last line, or, for a Mirage program, runs its image:

```sh
soma run examples/hello.soma
```

`soma build` checks one, deletes the files that checking makes, and keeps
(and prints) the image of a Mirage program;
`soma build -v` first prints the value of each line.

- `hello.soma`: hello world.
- `string_formatting.soma`: `to_string` on strings, numbers and lists, and
  a `greet` that accepts any of them.
- `compile_time_error.soma`: a wrong argument is rejected when the program
  is checked, before it runs.
- `run_time_error.soma`: the same mistake with an `Any` parameter is
  accepted, and fails when the program runs: `soma run` prints the value
  as far as it was computed, `"Hello, " ++ raise`, and the error,
  `Run-time error: expected a string, but got 42 : nat.`
- `basic_fibonacci.soma`: the textbook recursive `fib`, with `Recursive`
  and `match`.
- `gradual_fibonacci.soma`: a linear-time `fib`, first with its types
  inferred as `nat`, then with them written as Stdlib's binary `N` for large
  results.
- `recursive_countdown.soma`: why a recursive call on `n - 1` is rejected,
  and the `Succ m` countdown that is accepted.
- `type_functions.soma`: functions from types to types. `f` swaps
  ints and strings, `g` turns ints into even ints (a number with a proof
  that it is even), and `h` and `j` take arguments of the types they
  compute. The types are passed as codes (`Int`, `Str`), since a function
  cannot ask a type what it is. `type_functions.proof` proves that `j`
  cannot be given an odd number, and that it returns a larger number for
  any number above 1.
- `sqrt2_irrational.soma`: a proof that the square root of 2 is irrational
  (`irrational (sqrt 2)`), top down: the theorem first, then a proof that
  reduces it with `enough` to the rationals, to whole numbers, and to
  "`n * n` even means `n` even". `lia`, `nia` and `lra` do the arithmetic.
- `sqrt2_irrational_bottom_up.soma`: the same proof bottom up, as separate
  named lemmas proved before the theorem that uses them.
- `reason_components.soma`: Reason React components with JSX
  (`Require Import Reason.`): typed props, an untyped (`Any`) prop checked
  when the page is built, a fragment, rendered to HTML. What is proved
  about them (`Greeting` escapes any name) is in `reason_components.proof`.
- `reason_counter.soma`: a counter app (state, actions, a view);
  `reason_counter.proof` proves that its count stays within a limit,
  whatever buttons are clicked. Only the theorems have types.

A program's lemmas and theorems can be in `NAME.proof` next to
`NAME.soma`: building or running the program reads it after the program
and checks them, and fails if one does not hold.
- `mirage_*.soma`: MirageOS unikernels. A program that has
  `Require Import Mirage.` is built into an image, `<name>.hvt`, by `soma build`,
  which says how to run it (see the Mirage section of GRADUAL.md):
  - `mirage_minimal.soma`: the smallest unikernel, one line printed.
  - `mirage_minimal_web_server.soma`: the smallest web server, one page.
  - `mirage_hello.soma`: console output and a countdown with `sleep`.
  - `mirage_clock.soma`: the time of day every second, `forever`.
  - `mirage_http_server.soma`: an HTTP server, with `serve`, `now` and
    `random`.
  - `mirage_fetch.soma`: fetches a page from the server, with `args`,
    `fetch` and exit codes.

  `dev/mirage-check.sh` builds and runs them all.

Outside a proof, `Definition` can be left out: `greet name := ...` is
`Definition greet name := ...`. Recursive functions still need `Recursive`.

Outside a proof, a bare term such as `greet "world".` is evaluated and printed,
like `Eval lazy in greet "world".` Other strategies are still available:
`Eval cbv in ...`, `Compute ...` (the VM, which falls back to `cbv` under
`Gradual Typing`), and `Eval simpl in ...`, which only rewrites the term for
readability.
