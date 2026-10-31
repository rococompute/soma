# wasm_add

A program that uses functions written in Rust, compiled to WebAssembly.

```
add.wasm          the module: add and fib, of i64s (built from rust/)
add.definition    what Soma takes add.wasm to be
main.soma         Soma code built on add and fib
main.proof        what follows if add adds
model.soma        does add add? tested on sums small and large
rust/             the Rust crate; rust/build.sh builds add.wasm
```

## A module, and its definition

`rust/src/lib.rs` exports two functions, of `i64`s:

```rust
#[no_mangle]
pub extern "C" fn add(a: i64, b: i64) -> i64 { a.wrapping_add(b) }

#[no_mangle]
pub extern "C" fn fib(n: i64) -> i64 { ... }
```

`rust/build.sh` builds it for `wasm32-unknown-unknown` (`rustup target
add wasm32-unknown-unknown`) and copies it to `add.wasm`, which is kept
here, so that the example needs no Rust to run.

`add.definition`, next to `add.wasm`, says what Soma takes its exports to
be:

```
add : N -> N -> N.
fib : N -> N.
```

`Import add.` in `main.soma` compiles the two into the project's
`.soma-cache`, as it compiles any file it imports. Compiling checks the
declarations against the module: each name is one of its exports, with as
many arguments, and its numbers fit the declared types. Otherwise:

```
add.definition declares sub, which add.wasm does not export.
It exports add (i64, i64) -> i64, fib (i64) -> i64.
```

A declared type is `N`, `Z`, `Any`, or the module's own `i64` or `i32`.
A `.definition` only declares, and defines nothing; the stamp of the
cache has the digest of `add.wasm`, so a rebuilt module compiles what
uses it again.

## Using it

`add` and `fib` are then functions as any:

```
total (xs : list N) : N := fold_left add xs 0%N.
double (n : N) : N := add n n.
fibs (n : nat) : list N := map (fun k => fib (N.of_nat k)) (seq 0 n).
```

`soma build -v main.soma` computes them, running the module in the
WebAssembly reference interpreter: `10`, `42`, and the first twelve
Fibonacci numbers.

A call is checked against the declared types. Rust's `add` wraps around
past the largest `i64`, which an `N` cannot hold, and an `N` larger than
that cannot be given to it; either is a run-time error, saying what the
module gave or could not take:

```
add 9223372036854775807 1.
Run-time error: expected an N, but got Wasm.I64 (-9223372036854775808) : Wasm.i64.

add 9223372036854775808 0.
Run-time error: expected a Wasm.i64, but got 9223372036854775808%N : N.
```

A trap of the module is one too: `Trapped "unreachable executed"`.

## Proofs, and a model

Soma does not compute the module when it checks a proof: to the kernel,
`add` and `fib` are parameters, so no theorem holds by running Rust code.
`main.proof` proves what follows if `add` adds, with that as the
theorem's hypothesis:

```
Theorem total_sums : (forall a b, add a b = (a + b)%N) ->
  forall xs, total xs = fold_left N.add xs 0%N.
```

`model.soma` tests the hypothesis, with `Soma.Explore`, on sums small and
large. It does not hold for all of them, and `soma build model.soma`
fails, saying where:

```
Violation 1, from input (9223372036854775807%N, 1%N):
  "add.wasm's add is +" is a run-time error: expected an N, but got Wasm.I64 (-9223372036854775808) : Wasm.i64.
Violation 2, from input (9223372036854775808%N, 0%N):
  "add.wasm's add is +" is a run-time error: expected a Wasm.i64, but got 9223372036854775808%N : N.
...
No violation from: (0%N, 0%N), (2%N, 3%N), (1000%N, 2000%N),
  (4611686018427387904%N, 4611686018427387903%N),
  (9223372036854775807%N, 0%N).
```

`soma explore main.soma` lists the module's functions as escape hatches,
taken at their declared types:

```
Escape hatches, where static types are given up:
  add.add
    is add.wasm's add (i64, i64) -> i64, taken to be N -> N -> N, which each call checks
  add.fib
    is add.wasm's fib (i64) -> i64, taken to be N -> N, which each call checks
```

## Not yet

- An image: a Sandbox program whose `main` calls a module is refused
  when it is built, until the image has an interpreter.
- Exports of `f32` and `f64`, of several results, and modules that import
  functions (WASI): a `.definition` says so when it meets one.
- A `.wasm` without a `.definition`, as exports of type `Any`.
