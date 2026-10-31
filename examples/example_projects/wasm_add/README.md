# wasm_add

A program that uses functions written in Rust, compiled to WebAssembly.

```
add.wasm          a module: add and fib, of i64s; hypot and half, of floats (rust/add)
add.definition    what Soma takes add.wasm to be
mul.wasm          a module without a .definition: mul and average (rust/mul)
main.soma         Soma code built on add, fib and mul
image.soma        a unikernel whose main calls add.wasm
main.proof        what follows if add adds
model.soma        does add add? tested on sums small and large
rust/             the Rust crates; rust/build.sh builds both modules
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
here, so that the example needs no Rust to run; and `rust/mul` as
`mul.wasm`.

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
Run-time error: expected an N, but got I64 (-9223372036854775808) : i64.

add 9223372036854775808 0.
Run-time error: expected an i64, but got 9223372036854775808%N : N.
```

A trap of the module is one too: `Trapped "unreachable executed"`.

## Floats

`rust/add` also exports `hypot`, of `f64`s, and `half`, of an `f32`,
which `add.definition` declares as `float`s; `rust/mul` exports
`average`, of `f64`s, which is of type `Any`:

```
hypot : float -> float -> float.
half : float -> float.
```

```
hypot 3 4.                            (* 5 *)
half 2.5.                             (* 1.25 *)
(average 1%float 2%float : float).    (* 1.5 *)
```

A declared `float` makes `3` and `2.5` floats there; `average`, of type
`Any`, takes its arguments as they are written, so `1%float`: `average 1
2` is `expected a float, but got 1 : nat`, as a `nat` is no float. An
`f32` rounds what it is given (`half 0.1` is `0.05000000074505806`).
`Import add` gives `float` and its literals, which `Soma.Wasm` exports
with the module's types.

## A module without a definition

`mul.wasm` has no `.definition`: `Import mul.` takes it as it is, its
exports of type `Any`, which gradual types allow:

```
Check mul.                       (* mul : Any -> Any -> Any *)
area (w h : N) : Z := (mul w h : Z).
area 6 7.                        (* 42 *)
```

Soma numbers go in as `Any`s; what the module gives back is the number it
is, its `i64` as a `Z`. Using it as something else is a cast that fails,
as any: `(mul 6 7 : N)` is `expected an N, but got 42%Z : Z`, and an
`Any` that holds no number is no argument: `mul "six" 7` is `expected an
i64, but got "six" : string`. An export that a `.definition` does
not declare is of type `Any` in the same way.

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
  "add.wasm's add is +" is a run-time error: expected an N, but got I64 (-9223372036854775808) : i64.
Violation 2, from input (9223372036854775808%N, 0%N):
  "add.wasm's add is +" is a run-time error: expected an i64, but got 9223372036854775808%N : N.
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

## Inside a unikernel

`image.soma` is a Sandbox program whose `main` calls `add.wasm`'s
functions. `soma run image.soma` builds `image.hvt`, a MirageOS image
with the WebAssembly interpreter and `add.wasm` in it, and runs it:

```
add 2 3 = 5
fib 50 = 12586269025
hypot 3 4 is 5: yes
half 2.5 is 1.25: yes
```

Each call is checked against `add.definition` in the image as Soma
checks it when it evaluates, with the same messages: a sum that wraps
stops the image with `Run-time error: expected an N, but got I64
(-9223372036854775808) : i64`, a `"kind":"cast"` failure in its events
(`soma run --events`), which `soma run --supervise` sees as any other.

An export of type `Any`, such as `mul.wasm`'s, cannot be called from an
image yet: the build says so, and to declare it in `mul.definition`.

## Not yet

- Exports of several results, and modules that import functions (WASI):
  a `.definition` says so when it meets one.
- An export of type `Any`, in an image.
