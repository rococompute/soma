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

The same function three times, with more types each time. The numbers are
`N`s, natural numbers stored in binary. (`nat`, the other kind, counts in
unary, so a large one is slow and can overflow the stack.)

First with `Any`, the type of any value: whatever `x` is, it's checked to
be an `N` only when `x * x` runs. `12%N` writes 12 as an `N`, since an
`Any` argument doesn't say which kind of number it is.

```fsharp
square (x : Any) : N := x * x.

square 12%N.           (* 144%N *)
square (-3)%Z.         (* run-time error: expected an N, but got (-3)%Z : Z *)
```

Then with `x` typed as an `N`. Now `typed_square (-3)%Z` is rejected when
the program is checked, before anything runs, and `123` is read as an `N`.

```fsharp
typed_square (x : N) : N := x * x.

typed_square 123.      (* 15129%N *)
```

Then with a dependent type, one that depends on a value. The body is still
`x * x`; what changes is that the function takes a second argument,
`even`, a proof that `x` is even. Its type, `N.even x = true`, mentions
the first argument. The caller supplies the proof: `eq_refl` is the proof
that something equals itself (`a = a`), and the checker may compute both
sides first. For 2048, `N.even 2048` computes to `true`, so `eq_refl` fits
`true = true`. For 123, it would have to prove `false = true`, and doesn't.

```fsharp
gradually_typed_square (x : N) (even : N.even x = true) : N := x * x.

gradually_typed_square 2048 eq_refl.   (* 4194304%N *)
gradually_typed_square 123 eq_refl.    (* rejected: 123 isn't even *)
```

The rejected line fails when the program is checked: `The term "eq_refl"
has type "N.even 123 = N.even 123" while it is expected to have type
"N.even 123 = true"`. Leaving the proof out doesn't skip the check:
`gradually_typed_square 123.` is a function still waiting for it, `fun _ :
false = true => 15129%N`.

Soma doesn't invent proofs, but a type class can find this one by
computing, so the call looks like the ones above. `` `{Even x} `` is the
proof argument, filled in by trying `eq_refl`:

```fsharp
Class Even (x : N) := even_proof : N.even x = true.
#[export] Hint Extern 1 (Even _) => exact eq_refl : typeclass_instances.

even_square (x : N) `{Even x} : N := x * x.

even_square 2048.      (* 4194304%N *)
even_square 123.       (* rejected: Could not find an instance for "Even 123" *)
```

Either way, the proof is found while the program is checked, so `x` has
to be known then, as a literal is. For an `x` that arrives when the
program runs, the program checks `N.even x` first and carries the result
along as the proof.

Without the rejected lines, all four go in one file, `square.soma`: `soma
run square.soma` prints the last value, `= 4194304%N : N`, and `soma build
-v square.soma` prints each. `soma help` lists the commands: build, run,
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
