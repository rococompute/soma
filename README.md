# Soma

Soma is a programming language with gradual dependent types. Types can be
as loose as you like (`Any`, checked at run time) or as precise as a
proof, and a program's theorems sit beside it, in `FILE.proof`, and are
checked when it builds. A program prints its result, or is built into an
OCaml executable, a MirageOS unikernel or a JSX page, and it can use OCaml
and WebAssembly modules.

Its kernel implements GCIC^G: conservativity and graduality are kept, and
normalization is given up, so type checking may not terminate.
[GRADUAL.md](GRADUAL.md) describes the language, the `soma` command and
how it's built.

## Installation

```sh
curl -fsSL https://raw.githubusercontent.com/yevbar/soma/gradual/install.sh | sh
```

[`install.sh`](install.sh) builds Soma from source in `~/.soma` and puts
the `soma` command in `~/.local/bin`. It needs git, make, a C compiler and
opam 2.1 or later; opam installs the system libraries the build needs, and
the script installs git and opam with Homebrew or apt if they're missing.
The first run takes about 30 minutes and 3 GB: an OCaml 4.14.2 switch,
then Soma and its standard library. Run it again to update.

From a checkout, `./install.sh` builds that checkout in place:

```sh
git clone --depth 1 -b gradual https://github.com/yevbar/soma.git
soma/install.sh
```

`SOMA_REF` picks the branch, tag or commit, and `SOMA_DIR`, `SOMA_SWITCH`
and `SOMA_BIN` say where things go; the top of the script lists them. The
steps it runs are in [GRADUAL.md](GRADUAL.md#quick-start), and the build's
requirements in [INSTALL.md](INSTALL.md).

## A first program

The same function twice, from
[gradual_fibonacci](examples/example_files/gradual_fibonacci/gradual_fibonacci.soma):
first with no types written, then with the types chosen where they matter.

```rocq
(* No types: n is a nat from the patterns, and a and b are nats because
   + adds nats. *)
Recursive fib_loop n a b :=
  match n with
  | 0 => a
  | Succ m => fib_loop m b (a + b)
  end.

fast_fib n := fib_loop n 0 1.

fast_fib 20.           (* 6765 *)

(* A nat is unary, so a large result is slow. Writing the types makes the
   numbers added Stdlib's binary N, while n still counts steps as a nat. *)
Recursive big_fib_loop (n : nat) (a b : N) : N :=
  match n with
  | 0 => a
  | Succ m => big_fib_loop m b (a + b)
  end.

big_fib n := big_fib_loop n 0 1.

big_fib 100.           (* 354224848179261915075%N *)
```

`soma run fib.soma` prints the last value, `= 354224848179261915075%N : N`,
and `soma build -v fib.soma` prints both. Nothing else changes when the
types go in: the untyped version is checked as it is, and the written types
only say what the numbers are. `soma help` lists the commands: build, run,
explore, compile, extract, hash, search, diff, get and repl.

## Documentation

- [GRADUAL.md](GRADUAL.md): the language, the `soma` command, projects
  (`soma.toml`, dependencies by git tag), OCaml, WebAssembly, Sandbox
  (MirageOS) and JSX programs, and how the kernel's rules work.
- [examples/](examples/README.md): single-file programs and projects. Run
  one with `soma run examples/example_files/hello/hello.soma`.
- [gradual-coverage.md](gradual-coverage.md): what is gradual so far, and
  what isn't yet.
- [doc/](doc): the reference manual that came with the kernel, for the
  parts of the language Soma doesn't change.

## Versions

Soma has no releases yet: `gradual` is the branch to build, and its git
log says what changed. The kernel is Rocq 9.3.0's
(`tools/configure/configure.ml`) and Stdlib is vendored at V9.2.0. The
opam packages are `soma-runtime` (the kernel, the tools and the `soma`
command) and `soma-core` (the libraries). Behind `soma`, the binaries
(`rocq`, `rocqchk`) and the library names (`Corelib`, `Stdlib`) keep
their upstream names. [GRADUAL.md](GRADUAL.md#versions) has the details.

## Bug reports

Report bugs and feature requests in [the issue
tracker](https://github.com/yevbar/soma/issues). A good report says which
commit you built (`git -C ~/.soma log -1 --format=%h`), your OS and OCaml
version, and includes the smallest `.soma` file that shows the problem.

## Contributing

Soma's own tests are `test-suite/misc/soma_*.sh`, and the gradual tests
that [GRADUAL.md](GRADUAL.md#tests) lists; `make -C test-suite` runs the
whole suite. The [contributor's guide](CONTRIBUTING.md) came with the
kernel and covers its code.

## License

Soma is under the GNU Lesser General Public License 2.1: see
[LICENSE](LICENSE).

## Fork of Rocq

Soma is a fork of the [Rocq Prover](https://github.com/rocq-prover/rocq)
9.3.0, and keeps its license. For questions specific to Rocq, refer to
[Rocq's README](https://github.com/rocq-prover/rocq#readme).
