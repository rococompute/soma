# Soma: GCIC^G, the variant that gives up normalization

Soma's kernel is this fork of the Rocq Prover (based on 9.3.0). It adds
**gradual dependent types**, following

> Meven Lennon-Bertrand, Kenji Maillard, Nicolas Tabareau, Éric Tanter.
> *Gradualizing the Calculus of Inductive Constructions.* TOPLAS 44(2), 2022.

That paper proves a "fire triangle of graduality": a gradual extension of CIC
cannot have all three of

| property | meaning | this fork |
|---|---|---|
| **Conservativity** | on terms without `?`, it is exactly CIC | ✅ kept |
| **Graduality** | making types less precise never breaks a program, and casts form embedding–projection pairs | ✅ kept (by design, not mechanically proven here) |
| **Normalization** | every well-typed term terminates, so type checking is decidable | ❌ **given up** |

The paper names the three ways out GCIC^N, GCIC^↑ and GCIC^G. This fork
implements **GCIC^G**: the unknown type `?` at universe `i` can hold
`? -> ?` *at the same universe*, so self-application typechecks:

```rocq
From Corelib.Gradual Require Import Gradual.

Definition delta := fun x : Any => x x.
Definition omega : Any := delta delta.   (* well typed *)
Eval lazy in omega.                      (* does not terminate *)
```

Because conversion can run arbitrary computation, **type checking is
undecidable**. `Check (eq_refl : omega = unk)` does not terminate either.
So that the prover still answers, reduction stops after `Gradual Steps`
gradual reduction steps per command (100000 by default) with an error:

```
Gradual reduction exceeded 100000 steps (while reducing cast).
Normalization does not hold for gradual terms, so this may be a loop.
Raise the limit with "Set Gradual Steps <n>." or remove it with "Unset Gradual Steps."
```

Only steps headed by `cast`, `unknown` or `err` that make progress count.
The rest is CIC reduction, which terminates, so ordinary terms are not
affected. `rocqchk` runs without a limit by default, since it rechecks what
the kernel already accepted. `rocqchk -gradual-steps n` bounds each
declaration, against a tampered `.vo` whose gradual reduction loops.

## Quick start

```sh
opam switch create soma ocaml-base-compiler.4.14.2 --no-install
eval $(opam env --switch=soma --set-switch)
opam install --deps-only ./soma-runtime.opam
make dunestrap
dune build soma-runtime.install soma-core.install
_build/install/default/bin/soma run my_file.soma
```

The switch is a named one, kept in opam's root, and not a local switch in
the checkout (`opam switch create ./`): opam builds a package inside its
switch, and `wasm`'s build runs `dune build` without `--root`, so inside
Soma's checkout dune builds Soma's project instead, and fails with `Don't
know how to build wasm.exe`. `make dunestrap` writes the build rules of
the theories, whose dune files are generated rather than committed;
without it, the build makes no standard library (no `Prelude.vo`).

`soma-runtime.opam` is generated from `dune-project`. Its dependencies are
`dune` (>= 3.21), `ocamlfind` (>= 1.9.1), `zarith` (>= 1.11), and `wasm`
(>= 2.0.2); OCaml itself is >= 4.14.0, which 4.14.2 satisfies. On Linux
it also depends on `conf-linux-libc-dev`. `plugins/soma_wasm/dune` links
the `wasm` library, so the build needs that library.
`--deps-only` does not install the optional packages `rocq-native`,
`memprof-limits`, and `memtrace`. The test suite's dependencies
(`ounit2`, `conf-python-3`, `conf-time`) are in `soma-test-suite.opam`.

`soma` is Soma's command line (`topbin/soma.ml`):

- `soma build FILE` checks and builds a program as `rocq c FILE` does, with
  the same options, then deletes the files `rocq c` made (`.vo`, `.glob`,
  `.aux`), and prints the names of the files it keeps: the `.hvt` image of a Sandbox program. `soma build -v FILE`
  first prints the values of the program's bare terms. (`rocq c` keeps the
  `.vo`, for files that `Require` the program.)
- `soma run FILE [-- ARGUMENTS]` checks the program in a temporary
  directory, so that it leaves no files, and prints the value of its last
  bare term; a program that requires Sandbox is built into an image, which
  is run with ARGUMENTS (under `solo5-vmnet` when it uses the network).
  `--mem=MB` runs the image in MB megabytes (256, or `$SOMA_MIRAGE_MEM`,
  by default), and `--disk=NAME=FILE` attaches FILE as its disk NAME rather
  than `NAME.img`; a disk file that does not exist, or a disk the program
  does not name, is an error that says so.
- `soma repl [FILE]` is an interactive session (`rocq repl`, prompt
  `Soma <`), with FILE's definitions loaded first (`-l FILE`).
- `soma build --fill FILE` writes the proofs that `The rest follows.`
  found in `FILE.exp` (see Proof sentences).
- `soma explore FILE` reviews FILE and the project files it imports (see
  Exploring a program).
- `soma compile FILE` does both `soma build` and `soma explore`, in one
  check: it keeps what `soma build` keeps (a Sandbox program's image),
  then prints the review, and fails when it finds an issue or a violation.
- `soma help` lists the commands, and `soma build --help` the options of
  build and run (those of `rocq c`).

A program `FILE.soma` can have two files next to it, read in this order:

1. `FILE.ext`, its **extensions**: ways to extend the language before the
   program is compiled and verified, such as macros and readers (see
   Macros and Readers).
2. `FILE.soma`, the program.
3. `FILE.exp`, its **expectations**: what to expect of the program as
   written, its lemmas and theorems, checked after it.

They were `FILE.lang` and `FILE.proof`. A file left with its old name is
an error that says how to rename it, since it would otherwise go unread.

A program `FILE.soma` has its lemmas and theorems in `FILE.exp`, next
to it: a `.soma` or `.ext` file cannot start a proof (`Theorem`, `Lemma`,
a `Definition` proved interactively, ...; `vernac/vernactypes.ml`), while
Rocq's `.v` files can. Checking `FILE.soma` (`rocq c`, so `soma build` and `soma
run`) reads the program, then `FILE.exp` in the program's environment
(`toplevel/ccompile.ml`): the proofs see what it defines and imports, JSX
included, without importing anything. A proof that does not hold fails the
build, with its location in `FILE.exp`, and no `.vo` or MirageOS image is
made; the theorems are part of the program's library. `soma build
FILE.exp` and `soma run FILE.exp` stand for `FILE.soma`.
`examples/example_files/reason_counter/reason_counter.exp` and `examples/example_files/reason_components/reason_components.exp` are
examples; `test-suite/misc/soma_proof.sh` tests it.

### Proof sentences

A `.exp` file imports `theories/Soma/Proof.v` (and only a `.exp`
file does), so that a proof can be written as sentences that say what
each step does, for people and agents to read without replaying it.
Each sentence is checked: one that states the goal or a fact fails
unless it is the goal or holds, so the text cannot drift from the
proof.

```rocq
Theorem pow8_is_pow : forall x : nat, pow8 x = x ^ 8.
Proof.
  Take x : nat.
  We need to show that square (square (square x)) = x ^ 8.
  We conclude that x * x * (x * x) * (x * x * (x * x)) = x ^ 8.
Qed.
```

| Sentence | Checks, then does |
| --- | --- |
| `Take x : T.` | the next variable is a `T`; names it |
| `Assume that P as H.` | the next hypothesis is `P` (perhaps unfolded); names it |
| `Here H means that P.` | the hypothesis `H` is `P`, up to computation; shows it as `P` |
| `We need to show that P.` | the goal is `P`, up to computation; shows it as `P` |
| `It holds that P as H.` | proves `P` and names it |
| `It suffices to show that P.` | the goal follows from `P`; `P` is the new goal |
| `We conclude that P.` | the goal is `P`; proves it |
| `By t, ...` (the last three) | as above, with the hypothesis or lemma `t` (applied to arguments, if needed): `t` applied, or rewritten with |
| `Computing, we need to show that P.`, `Computing, we conclude that P.` | as without `Computing`, after evaluating the goal (`simpl`) |
| `We show that P as H.` | `P`, proved by the sentences in braces right after, is then `H` |
| `It suffices to show that P as H.` | the goal, proved from `H : P` by the sentences in braces right after; then `P` is the goal |
| `Choose x := t.` | proves an `exists x, ...` with `t` |
| `Obtain a and b from x.` | takes `x` (a pair, `{a \| P a}`, `exists`, `/\`) apart |
| `We prove each part.` | splits an `A /\ B` goal |
| `We consider each case of x.` | a case for each constructor of `x` |
| `We consider each case of x as H.` | the same, with `H : x = ...` in each case: what `x` is there |
| `We consider whether a < b as H.` (or `<=`, `=`) | for numbers, a case with `H : a < b` and one with its opposite; `a <? b` is then `true` or `false` |
| `We use induction on x.` | a case for each constructor of `x`, whose arguments and induction hypotheses each case takes and assumes |
| `We use strong induction on n.` | for a number: proves the goal for `n` assuming it for every smaller number, which is taken and assumed |
| `The rest follows.` | searches for the rest of the proof, and reports it as sentences (below) |

An example of what a function gives, `Example e : f 3 = "three".`, is
proved by `computed` (a tactic of `theories/Soma/Proof.v`), also under
`forall`s that the computation does not need to take apart: the kernel
computes both sides when the proof ends, at `Qed`, as it checks every
proof. `reflexivity` computes them as it is applied too, so it takes twice
as long, which shows in a file of many examples. An equation that does not
hold fails at `Qed`; a goal that is not an equation fails at `computed`.

`The rest follows.` searches for the rest of a proof
(`plugins/soma_proof/soma_rest.ml`): it takes and assumes what the goal
gives, then tries `soma_auto`, computing, the hypotheses, the program's
and its projects' lemmas, unfolding their definitions at the top of the
goal (not Rocq's), and Rocq's lemmas that could prove the goal, for 20
seconds at most. It reports the proof it found as sentences, each printed
so that it reads back as what it states. `soma build` says how many proofs
were found, `soma build -v` prints them, and `soma build --fill` writes
each in place of its `The rest follows.` in `FILE.exp`, indented as the
sentence was, so that the proof no longer depends on the search. When the
search finds nothing, the build fails with what is still to show, as
sentences to start from:

```
Error: The rest does not follow. Still to show:
    Take a : action.
    Take count : nat.
    Assume that count <= limit as H.
    We need to show that step a count <= limit.
```

`SOMA_REST_TRACE=1` prints the lemmas it tries. `test-suite/misc/soma_rest.sh`
tests it.

"Proves" is `soma_auto`: the hypotheses, computation, equalities,
`lia`, `ring`, `nia` and propositional logic; `By t` adds `t`, applied
or rewritten with. A step it cannot take is split into smaller
sentences. Sentences are tactics, so they mix with any other tactic. In
a `.exp` file, a tactic acts on one goal at a time (`Default Goal
Selector "!"`): with several goals open, each is focused with a bullet or
braces. Notations in a sentence are read as in a theorem's statement:
`*` is on `nat`s unless scoped, as in `(sqrt 2 * sqrt 2 = 2)%R`. All the
example `.exp` files are written in sentences, `sqrt2_irrational.exp`
(top down, with `It suffices to show that ... as ...` blocks and strong
induction) and `reason_counter.exp` (cases and induction) among them;
the tactics they replace are in their history.

### Record updates

Soma inherits Rocq's record update syntax, `{| r with f := v |}`.
For example:

```rocq
Record account := {
  owner : string;
  balance : nat;
  active : bool
}.

original : account := {| owner := "Ada"; balance := 10; active := true |}.
updated := {| original with balance := 25 |}.
updated_twice := {| updated with owner := "Grace"; balance := 30 |}.
```

Separate multiple field updates with semicolons. Fields not named are
copied unchanged: `updated` has owner `"Ada"`, balance `25`, and active
`true`; `updated_twice` has owner `"Grace"`, balance `30`, and active `true`.
Each update constructs a new record, leaving the original unchanged.

This replaces a helper that copies every field explicitly, such as:

```rocq
with_balance (r : account) (v : nat) : account :=
  {| owner := owner r; balance := v; active := active r |}.
```

Use `{| r with balance := v |}` in place of `with_balance r v`.
`examples/example_projects/record_update/main.soma` prints the fields after
both updates, without a full-copy helper. Run `soma build main.soma` in that
project, then `./main.exe`; it prints `Ada 25 true | Grace 30 true`.

### Macros: `.ext` files, a program's extensions

Macros are defined in `.ext` files, with `Macro name args := body.`: a
macro is a function from the code of its arguments (`args : list syntax`)
to the code it stands for (a `syntax`), in `theories/Soma/Macro.v`. A use
of a macro in scope, `name a b`, looks like a call: when it is
internalized (`interp/constrintern.ml`), the code of `a` and `b` is quoted
into `syntax` values, the macro is evaluated on them, and the `syntax` it
returns is read back as code and checked in place of `name a b`
(`vernac/somaMacro.ml`). A local variable of the same name hides the
macro. `syntax` has names, numbers, strings, applications, `fun`s, holes,
`let`s (`LetIn x value body`) and `match`es (`Match scrutinee branches`,
each branch a pattern and its body). A pattern is a name (a variable, or a
constructor such as `true`), a number, a string, `_`, or a constructor
applied to patterns (`Succ m`, `cons x _`). Other code (a notation like
`a + b`, a `match` with a pattern such as `(x, y)` or `[]`) is `Opaque`,
which a macro can return but not look into. A macro that returns a
`Match` can make structural recursion: `Recursive fact n := natcase n 1 m
(n * fact m).`, with `natcase` returning `match n with 0 => 1 | Succ m =>
n * fact m end`, passes Rocq's termination check. `MacroError "..."` fails the
expansion with that message, at the use; so does a run-time error in the
macro. Expansions nested 1000 deep stop with an error.

Macros are in scope only where they are asked for:

- `FILE.ext`, next to `FILE.soma`, is read before the program, so its
  macros are in scope in `FILE.soma` and `FILE.exp` (and in `soma repl
  FILE.soma`).
- Another `.ext` file is in scope where it is loaded, `Load
  "other.ext".`, or, compiled by itself (`rocq c other.ext`), where it
  is imported, `Require Import other.` (not with `Require` alone).
- `Macro` can only be used in a `.ext` file, and the `Macro` library
  (`syntax`, `App`, ...) is only in scope there: a `.ext` file is loaded in
  a module of its own that imports it.

`examples/example_files/macros/macros.ext` and `examples/example_files/macros/macros.soma` are an example;
`test-suite/misc/soma_macros.sh` tests it.

### Readers: other syntax, read from text

A macro is given code that Soma has already parsed, so it can only change
what that code means, not how it is written. A reader is given the text:
`Reader name text := body.`, in a `.ext` file, makes `name` a function
from a program's text (`text : string`) to its top-level forms (a `list
item`, in `theories/Soma/Macro.v`):

| Form | Runs as |
|---|---|
| `Def pos name body` | `name := body.` |
| `RecDef pos name params body` | `Recursive name params := body.`, which Rocq's termination check checks |
| `Expr pos term` | `term.`, a bare term, evaluated |
| `ReadError pos message` | reading fails with `message` |

`body` and `term` are `syntax`, as a macro returns, so a reader writes
`match`es and `let`s with `Match` and `LetIn`. `pos` is where the form
starts in the text, a count of characters, and an error in the form (a
`ReadError`, a type error, a recursion Rocq rejects, a name that is not
one) is reported at that line of the file. `chars` and `of_chars` turn a
string into the codes of its characters and back, so a reader can walk
its text as a `list nat`.

A reader in scope is used two ways:

- `Read name "text".`, anywhere a command can be, runs the forms there.
  The text is a string, its quotes written doubled.
- A file whose first line is `#lang name` is read by `name` whole: the
  rest of the file is the text, which Soma's parser never sees. The
  reader goes in `FILE.ext` next to it, or in a `.ext` file that
  `FILE.ext` loads. Such a file is compiled, run, and imported by
  another file of its project (`Import FILE.`) as any other is.

What a reader defines is in scope after it, in `FILE.exp`, and where
the file is imported; Soma's review counts it, and its escape hatches, as
it does the rest. The reader runs when the program is checked, as a
macro does: it is a Soma function, so it reads no file and has no
effect but its forms. `examples/example_files/lisp/` is a program in
s-expressions, `#lang lisp`, with its reader in `lisp.ext` and proofs
about what it defines in `lisp.exp`; `test-suite/misc/soma_readers.sh`
tests readers, and that example.

### Projects: `Import` compiles what it imports

A program can be several files in a folder, its project. In a Soma file,
`Import X`, where `X` is no module in scope, is the file `X.soma` (or
`X.ext`) of the project, and `Import X.Y` is `X/Y.soma`. It is compiled
into the project's `.soma-cache` (`.soma-cache/X/Y.vo`, the library
`X.Y`) unless the cache has it up to date, then loaded and opened, as
`Require Import` would. A name that is no file of the project is a
library, as before (`Import Sandbox`). One command cannot import both a
module in scope and a file or library. The project is the folder of its
`soma.toml` (below), the nearest above the file being built, or else the
folder of the program being built, so `soma build` and `soma run` (which
keep the cache) work from any folder (`vernac/somaImport.ml`, hooked in
`vernac/synterp.ml`).

A file is compiled by a `rocq c` of its own, which compiles what it
imports in the same way. Its `.exp` is checked then, and it is not made
a unikernel. When it succeeds, it writes a stamp next to the `.vo`: the
hash of the source, its `.exp` and its `.ext`, the digest of each
project file it imported, as compiled, and the digest of each library from
elsewhere it was compiled with (Stdlib, `Soma.JSX`, ...). A compiled file
is used while its stamp holds: its sources unchanged, what it imports up
to date and unchanged since, and the libraries the same, so that an
upgrade of Soma compiles the project again rather than failing on a
library compiled with the old one. A stamp of an older format is out of
date. So a change to a file compiles it again, and what imports it only when
its `.vo` changed, apart from its proofs: another proof of a statement compiles
nothing else, as no importer sees the body of a proof, and Rocq keeps proofs in
a segment of their own that its check of a `.vo`'s imports does not read. A `.vo`
keeps locations, so a change that moves lines does compile what imports it. Each
file is checked once per
compilation. A failed compilation leaves the cache as it was, and the
import fails with `Cannot import X.Y: X/Y.soma does not compile (its
errors are above).`, after its errors. A file that imports itself, through
others, is `Import cycle: a -> b -> a.`

The files of one `Import` (`Import a b c`), and what they import, are
compiled at the same time, one process each, rather than in turn; a file
that two of them import is compiled once, and the other waits for it.
`$SOMA_PROOF_JOBS` caps the number of proof checks at once (below), the
number of processors by default, and `SOMA_PROOF_JOBS=0` compiles one file
at a time, as before. With `SOMA_DEFER_PROOFS=1`, a file with a `.exp` is
compiled first without its proofs, so that what imports it can be compiled
at once, and its proofs are checked beside the rest of the build, at most
`$SOMA_PROOF_JOBS` at a time; the build waits for them at the end (`Checking
the proofs of X.exp, ...`), and fails with the errors of one that does not
hold. This is off by default: a library without its proofs is the same
library only when they add no universe constraints between global
universes, which Rocq keeps in the library, and many proofs about gradual
programs add some. The build then fails, saying that the library with its
proofs is not the one without them, and the build without
`SOMA_DEFER_PROOFS` works. `SOMA_PROOF_JOBS_KEEP=1` keeps the folder of
the checks' logs, and says where.

`soma build` also keeps a store of compiled projects, shared by the
checkouts of a machine: `$SOMA_CACHE`, or else `$XDG_CACHE_HOME/soma`
(`~/.cache/soma` without it), with a `.soma-cache` under a key of the
project's sources: the path and bytes of each `.soma`, `.exp`, `.ext`,
`.definition`, `.wasm`, `.ml` and `.lean` file, `soma.toml`, `soma.lock`, and
Soma itself. A checkout without a `.soma-cache` starts from the one of the
same key. A `.definition`'s `.vo` names the `FILE.ml` beside it by its path
in the project, so a program built from a `.vo` that another checkout
compiled uses its own checkout's `FILE.ml`, never the other's (a
dependency's `.ml` is named by its absolute path, in its own source).
The stamp's digest of that `.ml` is marked, so a stamp that recorded the
digest alone is out of date and the `.definition` is compiled again rather
than a `.vo` from before this, which named the `.ml` by an absolute path.
A project with a dependency on a folder (`{ path = "../wip" }`) is not kept in
the store, as that folder's files are not in the key.
`soma build --no-module-cache` does not read or write the store (the
project's own `.soma-cache` is still used). Deleting the store's directory
clears it. An empty `XDG_CACHE_HOME` is the same as unset: the store is
`~/.cache/soma`.

Toolchain freshness uses SHA-256 Merkle directory fingerprints: a directory
hash includes its sorted child names, kinds, permissions and hashes. The
private cache at `$XDG_CACHE_HOME/soma-fingerprints/v1` (otherwise
`~/.cache/soma-fingerprints/v1`) stores content-addressed directory nodes
and file-digest hints. Every invocation still lists directories and checks
file identity, size, modification time and change time. It reuses a file's
digest only when all metadata agrees; recent timestamps are rehashed to
avoid coarse-clock races. A parent directory's timestamp alone never
certifies an unchanged subtree. Symlink targets are checked too, and
cycles, changing inputs or unsupported files cannot certify freshness.

This replaces repeated reads of the installed libraries with metadata
scans when they are unchanged. Deleting or corrupting the fingerprint
cache is safe: Soma reads the content again. Set `SOMA_FINGERPRINT_CACHE=0`
for strict content reads on every scan, for example on filesystems whose
metadata cannot reliably report changes. These are fingerprints of build
inputs, not proofs that tests passed; test results still depend on the
compiler's recorded import graph and successful checks.

An unchanged native entry point can also reuse its completed checking and
extraction phases. The compiler certifies the exact generated files and loaded
libraries; the driver binds that certificate to the project, compiler,
environment and options before and after the build. A hit still takes the
generated project's lock, runs the ordinary native Dune validation, and copies
its current executable with the same mode as a normal build. It does not
declare the native product fresh: `soma build --check-fresh` still requires
native validation.

This first subset covers ordinary nonverbose, package-free native builds with
project-local OCaml implementations or the built-in Host module. Mirage,
JavaScript, external dependencies, selected startup rc files, source `Load`,
opaque embedded terms, unknown plugins and unsupported checking commands use
the full build. `--fill`, explicit exports, review and dependency-reporting
modes, verbose output and `--timings` also use the full path. Changed sources
and expectations are checked again; this is not incremental checking of edited
definitions. `soma check` retains its full checking behavior.

The certificates live in `$XDG_CACHE_HOME/soma-native-phases` (otherwise
`~/.cache/soma-native-phases`) and require the compiler's private content
receipts. Missing, edited or corrupt records cause a full build. Set
`SOMA_PHASE_DEBUG=1` to inspect eligibility and refusal diagnostics.

`test-suite/misc/soma_module_cache.sh`,
`test-suite/misc/soma_module_cache_checkout.sh`,
`test-suite/misc/soma_module_cache_path_deps.sh` and
`test-suite/misc/soma_module_cache_rebuild.sh` test it.

`examples/example_projects/cached_compilation` is an example;
`test-suite/misc/soma_import.sh` tests it. Not yet handled: two builds of
one project at the same time, and `soma run --supervise` of a program
that imports project files.

### The project: `soma.toml`

```toml
[project]
name = "rocq_stdpp"
version = "0.1.0"
description = "A shop's stock, kept in a finite map of the Rocq library stdpp"
```

A folder with a `soma.toml` is a project's root. Any file under it
imports from the root (`Import models.task` is `ROOT/models/task.soma`,
from `main.soma` or from `web/server.soma`, built by itself or not), its
`.soma-cache` is the root's, and the rules of its folders are those from
the root down. Without `soma.toml`, the root is the folder of the program
being built, as before (`vernac/somaProject.ml`, used by
`vernac/somaImport.ml`).

`[project]` says what the project is:

- `name`: what other projects, Rocq, OCaml and opam will know it by.
  Lowercase letters, digits and `_`, beginning with a letter, 64 at most;
  `-` is not allowed, as Rocq and OCaml names do not take it.
- `version`: the project's own version, a semantic version
  (https://semver.org): `MAJOR.MINOR.PATCH`, then `-PRERELEASE` and
  `+BUILD` (`1.0.0-rc.1+build.5`).
- `description`: what it is, in a sentence (optional).

`soma build`, `run`, `explore`, `compile` and `extract` check it. A key or
table Soma does not know is an error, not ignored, so a misspelling is
caught and a section Soma does not have yet is not mistaken for one it
acts on. Each error is `soma.toml:LINE: ...` with what to write instead:

```
soma.toml:2: "My-shop" is no project name: a name is lowercase letters, digits
and _, beginning with a letter (...), 64 at most: name = "my_shop"
soma.toml:3: "1.0" is no semantic version (https://semver.org): it is
MAJOR.MINOR.PATCH, three numbers, as 0.1.0 or 1.2.3
soma.toml:4: docs is not something soma.toml says (yet). soma.toml has
[project]: name (...), version (...), description (...), [dependencies]
("owner/repo" = "1.2.3"), and [opam] (cryptokit = "1.20").
```

`[opam]` gives the version of an opam package that the program's OCaml
libraries come from (below, "OCaml modules"), when the newest will not do:

```toml
[opam]
cryptokit = "1.20"        # its RSA functions changed in 1.21
```

A key is the package's name, as opam has it, and its value the version, as
`opam show PACKAGE` lists them. A package that `[opam]` does not name is
whichever version opam installs, the newest that fits.

`[image]` says how a MirageOS image of the project (a program that
requires Sandbox) is built and run:

```toml
[image]
memory = 4096             # megabytes, which soma run gives the image
text_start = "0xC0000000" # where its code is linked: 3 GB
user_memory = [{ name = "guest", address = "0x200000", size = "0xbfd00000" }]
```

- `memory`: the image's megabytes (256 by default), which the command to
  run it states and `soma run` gives it; `$SOMA_MIRAGE_MEM` and `soma run
  --mem=MB` come first.
- `user_memory`: hvt memory reserved for programs loaded by the unikernel.
  Each region has a unique alphanumeric `name`, a `size` in bytes, and an
  optional fixed `address`. Sizes and addresses are integers or hexadecimal
  strings, aligned to 64 KiB. Fixed regions must not overlap each other, the
  start of the image, or exceed configured memory. The tender validates the
  final image layout. User memory is executable and writable; the rest of
  guest memory keeps Solo5's W^X protections.
- `text_start`: the address the image's code is linked at, rather than
  solo5's 1 MB (`0x100000`): an image that loads code of its own below it
  (kykeon's guest Linux executables, linked at 4 or 16 MB) moves out of its
  way. It is a multiple of `0x10000`, `0x100000` or above, below `memory`'s
  end. Soma forwards both layout settings to Mirage's `register`; the current
  mirage-mac toolchain implements them through its manifest and
  `-z solo5-text-start=ADDR`, without rewriting installed linker scripts.
  Layout features require Mirage `4.11.2+hvf.2` and Solo5 `0.13.0+hvf.4`
  or later from the Mac overlay. Different layouts have separate generated
  projects; ordinary images still work without these optional arguments.

`soma extract` names the opam package after the project, and gives it its
version and description, and `[opam]`'s versions (`"cryptokit" {= "1.20"}`). The TOML is TOML 1.0 (`vernac/somaToml.ml`, as
Soma depends on no TOML library), without dates and times. Every project
under `examples/example_projects` has one; `test-suite/misc/soma_project.sh`
tests it.

A project that provides its own Mirage entry functor can generate the
configuration for `mirage configure` with `soma mirage-config DIRECTORY`.
The command prints `config.ml` using the project's checked image layout
and its ordered list of devices.

```toml
[mirage]
name = "my_image"
main = "Unikernel.Main"
packages = ["lwt", "cstruct"]
local_libs = ["support"]
devices = [{ block_file = "rootfs" }, "default_network"]
```

Here the job takes a file-backed block device followed by the default
dual-stack network. The entry functor's arguments follow the device
list. Packages, local libraries, and devices default to empty lists.

### Dependencies: other projects, by their git tags

A project depends on other Soma projects as a Go module does: by the path
it is fetched from, and a version that is a tag there.

```toml
[dependencies]
"owner/maps" = "1.2.3"                    # https://github.com/owner/maps.git, tag v1.2.3
"gitlab.com/group/shop/v2" = "2.0.1"      # https://gitlab.com/group/shop.git, tag v2.0.1
"git@github.com:owner/private.git" = "0.1.0" # SSH, with your existing key or agent
"ssh://git@host.com/group/other.git" = "1.0.0" # SSH URL spelling
"owner/wip" = { path = "../wip" }         # a folder on disk, for a project being edited
```

In a file, a dependency is its own `[project] name`, not its path, as
`Import` takes a qualid, which has no `/`: `Import maps.gmap.` is
`gmap.soma` of the project whose `name` is `maps`, and `Import maps.a.b` is
its `a/b.soma`. `soma get owner/maps@1.2.3` writes that line and resolves;
`soma get owner/maps` looks up the greatest tag of the path's major, and
`soma get` alone resolves what is written, from the tags rather than
`soma.lock` (`vernac/somaDeps.ml`).

**Paths.** A key is in quotes (`/` is no bare key of TOML). `owner/repo` is
on `github.com`, and `github.com/owner/repo` is the same path. A first
segment with a `.` is the host, and the rest may be subgroups. Major 2 and
above is the suffix `/vN`, a path of its own, so `2.0.0` is never taken for
a later `1.9.0`. A subdirectory of a repository is not supported: `soma.toml`
is at the root of the tag. Two majors of one project have one `name`, so a
build cannot have both yet.

**SSH and private repositories.** An explicit `git@host.com:group/repo.git`
or `ssh://git@host.com/group/repo.git` key fetches through SSH, using Git's
normal SSH configuration and agent. SSH and HTTPS spellings have the same
package identity (`host.com/group/repo`), so changing the transport keeps
the locked commit and cannot introduce a second copy. SSH hosts use the
standard port; configure a host alias in `~/.ssh/config` for a custom one.
Aliases need no dot: `git@work:group/repo.git` and
`ssh://git@work/group/repo.git` both use the SSH host `work` and lock the
package as `work/group/repo`.
For major 2 and above append `/vN` after the repository name, for example
`git@github.com:owner/private.git/v2`.

`soma get 'git@github.com:owner/private.git@0.1.0'` adds an SSH dependency;
without the final `@VERSION` it selects the latest compatible tag. SSH
versions also work with `soma diff`, for example
`soma diff 'git@github.com:owner/private.git@0.1.0' 'git@github.com:owner/private.git@0.2.0'`.

SSH fetches default to `ssh -oBatchMode=yes`, so authenticate and establish the
host's key before building. Existing `GIT_SSH_COMMAND` and `GIT_SSH`
settings are preserved. No token or private key belongs in `soma.toml` or
`soma.lock`.

**Versions.** The value is a semantic version, without build metadata. Its
tag is `vVERSION` or `VERSION`; if both exist they are one commit.

**Selection.** Resolving runs once, before any file is compiled. The version
of a path is the greatest that anything asks for (minimal version selection,
as Go's), except that a version this project names is the one it gets, which
must be at least what its dependencies ask for. A checkout is used whatever
they ask for, as Go's `replace` is, and only a project on disk can name one.
A cycle of paths, or two selected projects of one `name`, is an error, as is a
dependency named as a file or folder of the project that names it. Each error
says what to write.

**`soma.lock`**, next to `soma.toml`, has the commit of each version selected.
It is written by Soma, and committed. A build whose `soma.lock` matches its
`soma.toml` uses those commits, and the network only for one that is not on
disk, so a moved tag changes nothing until `soma get`, which says it moved.
With the source gone too, the locked commit is fetched by its id, or else from
all the host's refs, and a commit no longer on the host is an error, and never
what the tag is now. Otherwise it resolves the tags and writes `soma.lock`.

**Sources and what they compile to.** A source is in
`~/.cache/soma/src/PATH@VERSION-COMMIT/` (`$XDG_CACHE_HOME/soma`), without
`.git`, shared by all projects, and not written to. It compiles into the
`.soma-cache/.deps` of the project being built. A dependency is compiled as a
project of its own, with its folder rules and its proofs, and its imports are
its own files, then the dependencies its `soma.toml` names. A dependency of a
dependency cannot be imported without naming it, which the error says how to:
not by `Import`, even once it is loaded, nor by `Require` or `From ... Require`.
What a program refers to by its full name is not checked: after `Import a.a`,
`c.c.v` resolves, as in Rocq a loaded library's names are there for all. So
a project's file or folder cannot have the name of any project selected, which
would be the same library.
Its libraries are named after it, `maps.gmap`, so that the `util.soma` of two
projects are two libraries. A dependency's Rocq libraries are compiled once,
in the build's cache, and what imports it need not name them.

**A dependency is checked, not run.** Fetching runs nothing: no hooks and no
submodules, and git never asks for a password. Compiling a dependency, fetched
or a checkout, with its `.exp`, its own imports and the Rocq libraries it
names, refuses each command whose argument says where to write:

```
maps.gmap:5: Redirect writes a file. A dependency is checked, not run.
Redirect works when that project is built on its own.
```

These are `Redirect`, `Profile "FILE"`, `Print Universes "FILE"`,
`Extraction "FILE"`, `Separate Extraction`, `Extraction Library`, `Recursive
Extraction Library`, `Extraction TestCompile`, and `Set` of `Extraction Output
Directory` and `NativeCompute Profile Filename`. The gate is the role of the
compilation and not the text of the repository: `soma build` or `soma extract`
of that project on its own runs them, and so does this project of its own
files. A file a library needs in order to check is in its repository, or its
author's build makes it before the tag; who wants the OCaml names an `OCaml
Library`, or extracts a program they trust. What prints stays (`Extraction d`,
`Recursive Extraction d`, `Print Universes`).

This is not a sandbox. `Declare ML Module` takes only libraries already
installed, so a repository cannot load native code of its own, but such a
plugin does what it does (micromega opens scratch files when it loads). An
`OCaml Library` a dependency names is installed by opam when `main` uses it,
and its `.ml` files run when the program does. Depend on what you would run.
What it proves is checked by Soma's kernel, and `soma explore` reviews it with
the program, escape hatches included.

`examples/example_projects/scores` depends on `../tally`;
`test-suite/misc/soma_deps.sh` tests all of this, with local bare repositories
in the place of hosts (git's `url.insteadOf`).
`test-suite/misc/soma_deps_ssh.sh` exercises both SSH spellings, `soma get`,
locked refetches and the shared package identity. `owl_tictactoe` under
`examples/example_projects` consumes the optional `rococompute/soma-owl` package
over HTTPS (authenticate Git if repository access is restricted) and trains a small neural network using Owl.

### What a definition is: `soma hash`

`soma hash FILE` checks a program and prints a line for each definition of it,
and of what it imports of its project and its dependencies:

```
CONTRACT WITNESS NAME  assumes A, B
```

The hashes are of what the kernel checked and not of the file, as Unison's are
(`vernac/somaHash.ml`). A term's binders are indices, its elaboration has
happened, gradual casts included, and each constant or type it mentions is
replaced by that thing's hash, down through Corelib. So comments, layout, line
moves, binder names, and the file or folder it is in do not change them, and
one definition in two files, or a dependency's under its name, is one hash.

- The **contract** is what what mentions a definition depends on: its type, its
  body if it is transparent, and every assumption it rests on, through proofs.
- The **witness** is the contract, the proof, and the witnesses of what it
  mentions, all the way down.

So another proof of a statement changes its witness, and what mentions it keeps
its contract. A proof that begins to rest on more changes the contract too, and
that of all that mentions it: Soma's logic is inconsistent once `unknown` is
used, so what a theorem says is not all that matters. **`assumes`** lists them:
axioms, the gradual primitives, Lean's theorems, a module's exports, and any
definition checked with guard or positivity checking off.

An assumption is a leaf: its name and type, and for a foreign one what it is. A
WebAssembly export has the digest of its module's bytes, an OCaml value its
libraries and `FILE.ml`'s digest. A constructor's name enters its type's hash,
and the type's own does not: a `color` of `Red | Green` is not `bool`.

**What the hash does not decide.** It is not the cache, which stays the bytes of
files and their `.vo`s without their proofs (`soma-stamp 3`), for two reasons:

- A file does more than define. A notation, an instance, a hint or a tactic is
  not in the kernel's terms, and changes what its importers elaborate to. With
  `Notation "!!" := x1.` changed to `x2`, every hash of that file is the same,
  and a file that uses `!!` means something else.
- A `.vo` records the digests of the `.vo`s it was compiled against, and Rocq
  will not load it with others: `Compiled library imp1 makes inconsistent
  assumptions over library a`. A line move changes those digests.

Not hashed yet: a functor's body, and the constraints of monomorphic universes
(they are named by order of appearance, and the global graph is not in the
hash). An OCaml library's version is not in its leaf, as what is installed is
not yet a pin. The hash is SHA-256, as OCaml 4.14 has only MD5. The first line of
what is hashed is the format, `soma-hash 1`. `test-suite/misc/soma_hash.sh` tests
all of this.

### Finding things: `soma search`

`soma search QUERY [FILE]` finds definitions and theorems in a project and the
dependencies it names, or, with `FILE`, in what that file sees. A type says what
a definition does and a theorem's statement what it says, so they can be looked
for by their shape, as Hoogle and Loogle do:

```console
$ soma search discount
pricing-1.1/rates.soma:4: pricing.rates.discount : nat -> nat -> nat
main.exp:2: main.nothing_lost : forall percent price : nat, percent <= 100 -> ...
  assumes pricing.rates.discount_small
pricing-1.1/rates.exp:2: pricing.rates.discount_small : forall percent price : nat, ...
  is assumed, and not proved

$ soma search 'list nat -> nat'
pricing-1.1/totals.soma:3: pricing.totals.subtotal : list nat -> nat
Stdlib.Lists.List.list_max : list nat -> nat
pricing-1.1/totals.soma:12: pricing.totals.invoice : nat -> list nat -> nat
```

A word is a name: the thing of that name first, then this project and what it
depends on before libraries, names that contain it, and what mentions it. A word
that matches nothing shows the names close to it, and says so. Anything else is
what `Search` takes (`"part"`, `-pattern`, several at once), and a type without
its parentheses: what matches all of the type first, then its conclusion, then
a part of it. `(vernac/somaSearch.ml)`

- `--no-assumptions` keeps what rests on nothing but the kernel. An axiom is a
  result like any other to `Search`; here it says so, and what rests on it does.
- `--json` is an object to a line, for an agent: `name`, `type`, `match` (`exact`,
  `name`, `conclusion`, `mentions`, `part`, `similar`), `scope` (`project`,
  `dependency`, `rocq-library`, `library`), `file`, `line`, `assumes`, `contract`.
- `--limit N`, 20 by default, and 0 for all.

It compiles what is not compiled yet, as a build does, into the project's
`.soma-cache`. A file that does not compile is left out and said to be, on
stderr, so it works while a file is being written.

**What it does not do.** It matches what is written, and does not unfold:
`_ * _ / _` does not find a theorem about `discount`, which is that. It sees what
is loaded: of Corelib and Stdlib what the project's files use, and what the
dependencies it names bring along, which it cannot itself import. A notation or a
name that only a file imports is known with `FILE`, as importing that file does
not bring it: `soma search '<[_ := _]> _ !! _ = _' main.soma`.
`test-suite/misc/soma_search.sh` tests it.

### What changed: `soma diff`

`soma diff OLD NEW` compares two versions of a project, each a tag,
`owner/repo@1.2.0`, or a folder with a `soma.toml`. A version number says what
its author meant, and a commit which bytes it is; this says what the kernel
checked:

```
pricing-1.0 -> pricing-1.1

The same, and resting on more (what uses it still builds):
  rates.discount_le, now assumes rates.discount_small

Edited:
  totals.shipping

Changed by what they use:
  totals.invoice

Another proof, or one beneath it, of the same statement:
  totals.subtotal_app

Added:
  rates.discount_small

3 unchanged. Notations, instances, hints and tactics are not compared.
```

A definition is **edited** when what it says itself differs, with what it
mentions taken by name, and **changed by what it uses** when it does not, and
what is beneath it does, so that one edit is not reported as all that is above
it. One with the same contract under another name is **moved or renamed**.

Each file of a version is compiled as a dependency, of a project made for the
purpose in a temporary folder (`vernac/somaDiff.ml`). So it is checked and not
run, the commands that write are refused, and nothing is written to the version.
A file that does not compile is reported, and the others are still compared. A
file in a folder that is no name, or in a project inside this one, is left out.
Both versions are hashed in the one run, so nothing depends on hashes being
the same on another machine, and `soma.lock` is not touched.

It reports and does not judge, and exits 0 whatever it finds: that a definition
was edited may be the point of the release.
`examples/example_projects/upgrade_check` is an example;
`test-suite/misc/soma_diff.sh` tests it.

### The rules of a folder

`X/X.ext` is the rules of the folder `X/`, and `X/X.exp` their
proofs, unless `X/X.soma` exists, whose `.ext` and `.exp` they then
are. Every Soma file under `X/`, in its subfolders too, is compiled as if
it started with `Import X.X`, after the rules of the folders around `X/`
(the project's own first: `ROOT/NAME.ext`, by its `soma.toml`'s name, or
`ROOT/ROOT.ext` without one). So what the rules define,
macros and theorems included, is in scope in those files and their
`.exp`s, and it is one library, compiled once into `.soma-cache` with
its proofs checked, and recompiled when it changes, as any import
(`folder_rules` in `vernac/somaImport.ml`, called from
`toplevel/ccompile.ml`). The rules of a nested folder see those of the
folders around it. A file is not given its folder's rules by importing a
file that is.

The folders are those from the project to the file. In a project with a
`soma.toml`, a file built by itself has the rules of the folders from the
root to it. Without one, a file built by itself is its own project, so
the rules of the folders above it do not apply; a warning says so, and a
`soma.toml` or `SOMA_PROJECT_ROOT` sets the project. A `X/X.exp`
without `X/X.ext` is an error.

`examples/example_projects/folder_rules` is an example;
`test-suite/misc/soma_folder_rules.sh` tests it.
`examples/example_projects/sexp_html` gives a folder a language of its
own: its rules define macros, `sexp` and `app`, that read HTML written as
s-expressions, `(div (h1 "Hello world"))`, into JSX elements and apps,
and hold the state of every app of the folder, a count that only +1
changes. Their proofs show, once and for every app of the folder, that
the state is the number of clicks and strictly increases.
`examples/example_projects/counter_server` serves such a counter from a
unikernel: a project whose `main.soma` requires Sandbox is built into an
image like a single file, with what it imports. Each request starts the
counter at the count in its address or its cookie, or at 0; the proofs
show that only whole numbers 0 or more are accepted, and that from any
accepted start the state strictly increases. `dev/mirage-check.sh`
asks the running image (`counter-server`).

A type declared in a Soma file is data: `Inductive action := Increment.`
is a `Type`, where Rocq, in a `.v` file, would make a type of one
constructor whose arguments are proofs (here, none) a proposition, as
`True` is (`vernac/comInductive.ml`). `: Prop` makes it one.

### WebAssembly modules: `.definition`

A WebAssembly module `FILE.wasm` is used through `FILE.definition`, next
to it, which declares what Soma takes its exports to be, one per line:
`add : N -> N -> N.` (`vernac/g_vernac.mlg` reads `name : type.` there
as a parameter; `theories/Soma/Wasm.v`, `plugins/soma_wasm`). `Import
FILE` compiles the pair into the project's cache as any imported file,
the stamp having the module's digest. Compiling checks each declaration
against the module: it is an export, with as many arguments, whose
`i32`s, `i64`s, `f32`s and `f64`s the declared types fit; a declared
type is `N`, `Z`, `float` (an `f32` rounds), `Any`, or the module's own
`i64` or `i32` (of `Soma.Wasm`, which a `.definition` exports, with
`float` and its literals). A `.definition` defines nothing, and
proves nothing (its `.exp` may).

The declarations are parameters to the kernel, which never computes
them: no proof holds by running the module. Soma computes them when it
evaluates a term, a bare term or an `Explore` model
(`vernac/somaForeign.ml`): a call whose arguments are numbers is run by
the WebAssembly reference interpreter (opam `wasm`), and replaced by
what it returns, as a value of the declared type. What does not fit is a
cast that fails, and so a run-time error saying so: a negative number
for an `N` (`expected an N, but got I64 (-9223372036854775808) :
i64`), an argument too large for the module (`expected an i64,
but got 9223372036854775808%N : N`), a trap (`Trapped "unreachable
executed"`). `soma explore` lists each declared export as an escape
hatch. Not yet: several results, and imports (WASI).

A Sandbox program whose `main` calls a module's functions is built into
an image that runs them (`toplevel/somaMirage.ml`): each declared export
is extracted as a call of `soma_wasm.ml`, generated in the MirageOS
project with the modules' bytes, which runs them with the same
interpreter (the image's project has the opam package `wasm`; a program
that calls modules has a project of its own, `plain-wasm` or `net-wasm`,
so that the others do not fetch it) and checks the declared types as
Soma does when it evaluates, with the same messages: a failure is a
failed cast (`"kind":"cast"` in the image's events). Floats are OCaml's
in the image (a generated `float64.ml`, and ExtrOCamlFloats' commands
for floats). An export of type `Any` cannot be called from an image yet,
as the image cannot read the numbers an `Any` holds: such a program is
refused when it is built, saying to declare the export in its
`.definition`.

An export that the `.definition` does not declare is declared as a
function of `Any`s, `Any -> Any -> Any`, and a `FILE.wasm` without a
`.definition` is imported so, as if its `.definition` were empty (which
`Import` writes in the cache): gradual types make a module usable as it
is. Numbers go in as `Any`s, and what it gives back is the number it is,
its `i64` or `i32` as a `Z`; an `Any` holding no number is an error
(`expected an i64, but got "two" : string`).

### OCaml modules: `.definition` next to `.ml`, or next to nothing

An OCaml module `FILE.ml` is used through `FILE.definition` too
(`theories/Soma/OCaml.v`, `plugins/soma_ocaml`). A `.definition` next to
no module declares the module of a library instead, named after the file:
`async.definition` declares `Async`, with `OCaml Library "async".`, the
findlib library it is. Its Soma modules are the OCaml module's
submodules: `Module Deferred. map : ... End Deferred.` declares
`Async.Deferred.map`. `name : Type.` (or `Type -> Type`, ...) declares one
of its types, and `name : type.` one of its values. The plugin turns each
value's declared type into an OCaml type when the definition is compiled:
`string`, `bool`, `unit`, `list`, `option`, products, `float`, `nat`,
`word64` (Soma.Word64's, OCaml's `int64`), `buffer` (Sandbox's, OCaml's
`bytes`), `promise A` (Sandbox's, an `'a Lwt.t`, in an image only),
functions, the declared types, and type variables (`forall A`, erased by
extraction). Anything else is refused there, `Any` among them. An OCaml
value carries no type at run time that a cast could check, so it has one
static type, unlike a WebAssembly module's numbers. A named argument,
`forall (attrs : list Attr.t), ...`, is OCaml's labeled one, `~attrs`
(also for an optional `?attrs`). Soma gives every argument by position.
A label left undeclared is given in its place, and undeclared optional
arguments are left out, as OCaml allows in an application of all the
arguments.

Soma never computes them, neither the kernel nor the evaluation of a
term. A `.soma` program whose `main` uses them is built with them after
it is checked (`toplevel/somaOcaml.ml`). `main` is extracted (with
`ExtrOcamlBasic`, `ExtrOcamlNativeString` and `ExtrOcamlNatInt`, as an
image is, so that strings, lists, options, pairs and `nat` are OCaml's,
`nat` its `int`, and `Nat.add`, `mul`, `sub`, `leb`, `ltb`, `div`,
`modulo` and `String.length`, `get`, `substring` and `compare` are
OCaml's, which
otherwise count a character at a time and copy the rest of the string at
each one: a program need not say how numbers run), each declared value being its binding in a
generated `soma_bindings.ml`. That binding is the value at its declared
type, with rigid type variables (`'a 'b. ...`), applied to its arguments
with their labels, so that OCaml checks each declaration against the
module. The project's `.ml` files go next to it. dune then builds them with
the libraries, from an opam switch that Soma makes in `~/.cache/soma/ocaml`
and installs them into, once (or `$SOMA_OCAML_SWITCH`), at the versions
soma.toml's `[opam]` gives. Soma asks opam what the switch has before
installing anything, so a switch made in advance (a CI image's, given by
`$SOMA_OCAML_SWITCH`) is used as it is, with no network. A program whose
libraries depend on js_of_ocaml is built into `PROG.js`, with `PROG.html`,
the page that runs it, which `soma run` serves on localhost. The others
are built into `PROG.exe`, which `soma run` runs. `soma explore` lists the
declarations as escape hatches.

`soma extract PROG.soma [-o DIR]` writes that project into DIR
(`PROG-ocaml` by default): `prog.ml`, `soma_bindings.ml`, the project's
`.ml` files, dune's files, and an opam file of the packages the libraries
come from. dune builds it with or without Soma, and a `main` that is a
string is printed. A program that requires Sandbox is not extracted so,
yet.

`examples/example_projects/async_tasks` calls Async, and
`examples/example_projects/bonsai_counter` is a counter of JSX run by
Bonsai in the browser, with no OCaml code of their own.
`dev/ocaml-check.sh` builds and runs both. A `nat` is given to OCaml as
extraction has it, OCaml's `int`, which is `Soma_nat.nat` to the
project's modules (a generated `soma_nat.ml`), and not converted:
`examples/example_projects/ocaml_succ` declares `succ : nat -> nat`. Rocq's
primitive 63-bit `int` (`PrimInt63.int`, which `Soma.OCaml`, and so every
`.definition`, names `int`, with its literals) is given as OCaml's `int`,
which is `Uint63.t` to the project's modules (a generated `uint63.ml`), and
not converted either; `Soma.Show` shows one, unsigned, in decimal. Not yet:
the other numbers (`N` and `Z`); OCaml's modules as values (Bonsai's `state_machine0` takes
the state's type as a module of the `Model` signature, so the counter's
state is a `Bonsai.Var`); labeled arguments of a function given to OCaml;
values named by a keyword of Soma's (`return`).
`examples/example_projects/wasm_add` uses a module built from Rust;
`test-suite/misc/soma_wasm.sh` tests it.

### Native library effects

`Require Import Soma.Native.` provides effects for extracted libraries without
making the program a Sandbox image. `program A` describes execution; `Export`
turns a program into an `entry A` at a native caller boundary. In generated
OCaml, a program is a thunk and an entry has the ordinary result type `A`.
The generated project includes the shared `soma_effect.ml`, handles and Lwt
dependency. No project-specific OCaml interpreter is required.

`Return`, `Invoke` and `Bind` express synchronous sequencing. `Invoke f next`
calls `f ()` exactly once, then continues with its value, including when that
value is `unit`. `Loop` advances through `Continue state` until `Finish result`
with no implicit bound or asynchronous bind. `Protect` and `Throw` retain
ordinary synchronous exception scopes. Programs and entries are data in the
logic: there is no evaluator `program A -> A`, no termination axiom and no
disabled guard check. Extracted code cannot pattern-match programs or entries,
because their native representations are executable code and results rather
than the logical constructor layout.

`Promise_return`, `Promise_map`, `Promise_bind`, `Promise_catch`,
`Promise_finally` and `Promise_fold` select the corresponding native Lwt
scopes. Map/bind take a provider thunk and an entry-returning callback; their
provider is invoked before entering Lwt's map/bind. This keeps a provider's
synchronous throw distinct from a promise rejection or callback failure.
Pure synchronous preparation can therefore precede a returned promise without
introducing extra asynchronous scopes. `result A E` has the native
`Stdlib.result` representation. Native signatures can name `entry A` and
`program A` after requiring `Soma.Native`, and `opaque value` is a
value-preserving native liveness barrier.

`examples/example_files/native_effects` exposes callable library functions.
`test-suite/misc/soma_native_effects.sh` builds the generated project, calls
its entries from both native and bytecode clients, checks a million-step
loop, exception scopes, aliases, cleanup, cancellation, task context and
provider release, and checks foreign callback signatures. `SOMA_TEST_HVF=1`
also boots a native caller of a generated entry in Solo5. These shared
execution primitives remain part of the trusted runtime; the tests do not
constitute a proof of native execution or Lwt semantics.

### Declarative native polymorphic variants

A `.definition` can describe an existing closed OCaml polymorphic variant
without a companion implementation:

```coq
From Soma Require Native.
OCaml Native Polymorphic Variant reply :=
 [ "Data" : string; "Eof"; "Error" : string ].
OCaml Native View view_reply :
 reply -> Native.result string (Native.result unit string).
OCaml Native Construct data : string -> reply := "Data".
OCaml Native Construct eof : unit -> reply := "Eof".
```

Soma emits the corresponding closed OCaml row type
and typed constructors/matchers. The logical handle is opaque; call each
operation with `Native.Call_callback`. The view is an ordered, right-nested
`Native.result` over payloads, using `unit` for nullary tags and the final
payload directly. Payloads retain their native identity, including mutable
objects and callbacks. A nullary tag and a tag carrying `unit` remain distinct
native layouts. Schemas are monomorphic and nonrecursive; duplicate/invalid
or colliding tag hashes and mismatched operation signatures are rejected.
Declarations have checked bodies and introduce no new logical axioms or
native evaluator. Native implementations remain part of the trusted boundary.

`native_variants.manifest` binds each logical symbol to its schema source and
generated module hashes. Payload-type dependencies are retained even when a
consumer uses only a nullary constructor. The
[`native_variants` example](examples/example_projects/native_variants/main.soma)
and [`dev/native-variant-check.sh`](dev/native-variant-check.sh) check native
and bytecode layouts, borrowed aliases, callback/promise identity, Weak roots,
logical hashes, rejected signatures and optional actual Solo5 execution.

`SOMA_OCAML_BINDINGS_MODULE=Kernel_network_bindings` gives the generated
binding module a distinct name when composing extracted libraries. It applies
to native extraction and Mirage generation, preserves logical program hashes,
and rejects malformed names or collisions with generated/caller modules.
The default remains `Soma_bindings`.

`Native.Raise_invalid_argument message` raises the original native
`Invalid_argument` with its borrowed message, preserving exception and
promise-map failure boundaries.

### Typed native callables

A `.definition` can retain a native function's labelled ABI as an opaque
value, without a handwritten adaptation function:

```coq
From Soma Require Native.
OCaml Native Callable normalizer := forall (cwd : string), string -> string.
OCaml Native Apply normalize : normalizer -> string -> string -> string.
```

The generated type is `cwd:string -> string -> string`. A record or caller
can store the original native function directly, preserving its identity.
`Native.Call_callback normalize (target,(cwd,path))` applies it with the
declared label. The Source call is positional; the typed generated binding
supplies the native labels. Callable schemas are monomorphic, nondependent
signatures with at least one argument; named binders are labels, and arrow
arguments are positional. `Apply` signatures must match the schema exactly.

An `Optional` clause lists the binders that use OCaml optional labels.

```coq
OCaml Native Callable reader Optional limit :=
  forall (limit : option string), string -> string.
OCaml Native Apply read : reader -> option string -> string -> string.
```

The generated callable type is `?limit:string -> string -> string`.
Pass `None` to omit the argument and use the native default, or pass
`Some value` to supply it. The generated binding forwards the option with
`?limit`, preserving the callable's argument order.

`OCaml Native Wrap` builds a labelled callable from a positional
`Native.callback` chain. The declared arguments and result must match the
callable, including the option types for optional labels.

```coq
OCaml Native Wrap wrap_reader :
  Native.callback (option string) (Native.callback string string) -> reader.
```

The generated wrapper applies each argument through the last labelled
argument at its original stage. It returns any remaining positional tail
directly, preserving that function's identity.

Schemas retain checked type dependencies and have no logical evaluator or
new axiom. `native_callables.manifest` records source and generated-module
hashes; changing labels changes the logical declaration identity. The
[`native_callables` example](examples/example_projects/native_callables/main.soma)
and [`dev/native-callable-check.sh`](dev/native-callable-check.sh) check native
and bytecode labels, aliases, exceptions, promise/context/cancellation behavior,
Weak roots, signature rejection and optional actual Solo5 execution.

### Inserting OCaml source

`soma insert FILE.ml --out DIR` translates OCaml into editable `.soma`
source. It uses OCaml's parser and type inference in a separate frontend
(`topbin/somaInsert414.ml`, selected by Dune), then checks
the result with ordinary `soma check`.
The source is never evaluated; PPX is not run. This is source migration,
separate from the OCaml bindings above, which keep their implementation in
OCaml. No placeholders, axioms or gradual holes stand in for missing code.

```sh
soma insert helpers.ml --out helpers-soma
soma insert path/to/ocaml --partial --out migrated --report migration.json
soma insert path/to/ocaml --partial --report-only --json
```

The initial subset includes inferred polymorphic pure functions, immutable
records and variants, tuples, lists/options/results, matches, selected Stdlib
operations and structurally checked list recursion. Simultaneous pure bindings,
string concatenation, signed integer formatting and list predicates are included.
OCaml `int` is a primitive
63-bit word, with wrapping arithmetic and signed comparisons, rather than an
unbounded `Z` or saturating `nat`. Values are prefixed `oc_`, types `oct_`,
constructors `occ_`, and fields `ocf_`; punctuation in names is hex-escaped.
Generated files are ordinary Soma and may be edited and strengthened afterward.
Value and function bodies use `ml { ... }` blocks: local pure bindings print as
`let ... = ... in ...`, parallel bindings as `let ... and ...`, and lambdas
and matches use `->`. Parallel bindings no longer need synthetic temporaries
unless they also destructure patterns. Signatures, data declarations and the
small support definitions retain ordinary Soma syntax. Record fields can
re-enter ML blocks for compound field expressions. This output change preserves
the existing primitive integer and library mappings; it does not translate
previously unsupported mutation or effects implicitly.

Unsupported constructs have source locations and diagnostic codes. Default
mode writes no Soma source if any input remains unsupported. `--partial` keeps
independently translated declarations that pass checking, and still exits 1
when anything remains. Users of omitted declarations are omitted too, rather
than linked to fake implementations. Effects, mutable state, exceptions,
nonstructural/local recursion and native bindings need further translation
rules. The JSON report lists checked item counts and diagnostics per file;
those counts measure declarations, not lines or behavioral coverage.

Directory input preserves relative paths and inventories files independently;
cross-module translation and linking are not implemented yet. `-I DIR` supplies
OCaml interface lookup directories; these must match the frontend's compiler
version. The first typedtree adapter supports OCaml 4.14 on 64-bit hosts.
On OCaml 5 builds the new command reports the missing adapter; the other Soma
commands remain available. Kernel checking checks the generated program's types
and expectations, rather than proving its equivalence to the OCaml source.
Existing destination files are never
overwritten. `--report-only` writes no Soma source; `--report FILE` can preserve
the inventory. Exit 0 means the input translated completely, 1 means migration
is incomplete, and 2 means an invocation or destination error.

`test-suite/misc/soma_insert.sh` checks synthetic OCaml reference behavior
against kernel-checked expectations for generated Soma, and checks incomplete
migrations, non-evaluation, shadowed library names, recursion and destinations.
`dev/insert-kykeon-check.py --kykeon ../kykeon --report /tmp/kykeon-insert.json`
compares actual Kykeon allocator helpers against inserted Soma, then inventories
the complete unikernel source without editing Kykeon or launching agents/VMs.
`dev/insert/kykeon-baseline.json` records the initial target measurement, with
source hashes: 74 of 686 top-level items across 29 files checked independently.
These include constants, data types and pure helpers; they do not constitute
a translated Kykeon application. The largest remaining diagnostic category
is unavailable OCaml module/type information, followed by unsupported type,
library, native-binding and effect translations.

Soma source files end in `.soma`. `rocq c`, `Load`, `-l` and `rocq dep`
also accept Rocq's `.v` (Corelib and the Rocq libraries are `.v`), and
`.ext`; given a name without an extension, they look for `.soma` first,
then `.v`, then `.ext`.
`rocq makefile`, `rocq doc` and editor modes still only know `.v`.

Every file starts with the Soma prelude, `theories/Soma/Soma.v`,
loaded right after Rocq's Prelude. It exports, from `theories/Soma`:

- `Corelib.Gradual.Gradual`, which sets `Gradual Typing`.
- `Strings.v`: `"..."` is a Stdlib `string` (a list of ascii characters)
  everywhere, with `string` and `append` in scope, so Stdlib's string
  functions apply to literals.
  `s ++ t` appends strings wherever a `string` is expected (argument scope
  `str`); elsewhere `++` appends lists.
- `Lists.v`: `[1, 2, 3]` list literals, also used when printing.
- `Show.v`: `to_string`, a method of the type class `Show`, with instances
  for `string`, `bool`, `nat`, `N`, `Z` and `list A`. `Hint Mode Show +`
  makes instance search wait until the type is known.
- `Succ`, another name for the `nat` constructor `S`, usable in patterns and
  used when printing.
- `x != y`, another spelling of `x <> y` (not equal), used when printing.
- Stdlib's `NArith`: the binary natural numbers `N`, their literals and
  arithmetic. `nat` stays the default for number literals.
- Stdlib's `Arith` (`nat` comparisons such as `=?` and `<?`, `mod`),
  `List` (`map`, `seq`, `filter`, `fold_left`, ..., and `++` and `::` on
  lists) and `Lia` (the `lia` and `nia` tactics).
- Stdlib's `ZArith`: integers `Z`. Rationals `Q`, reals `R` with `sqrt`,
  `Q2R` from rationals to reals, and the `lra` tactic (`QArith`, `Reals`,
  `Qreals`, `Lra`) are opt-in, not in the prelude: write
  `From Stdlib Require Import QArith Reals Qreals Lra.` to use them.
  `QArith` opens `Q_scope`, so rationals are written `(1 # 2)%Q` and reals
  `(sqrt 2)%R`.

It also sets `Automatic Generalization` (`vernac/comDefinition.ml`): a type
that a `Definition` leaves unknown becomes a maximal implicit type parameter,
followed by the type class instances that depend on it, as in ML's
let-generalization. `Definition greet name := append "Hello, " (to_string
name).` is `greet : forall {A : Type}, Show A -> A -> string`. Any other
unsolved evar is still an error, and `Fixpoint`/`Recursive` are not
generalized. Under the same flag, a bare term or `Eval` fails if an instance
whose type is known is missing (`to_string tt`: no `Show unit`) instead of
printing a stuck term.

GCIC makes an implicit argument whose binder occurs nowhere in the rest of
the function's type `?`, since nothing could determine it. A type class
instance argument is the exception: its binder never occurs, but instance
resolution determines it (`pretyping/pretyping.ml`, `erased`).

An application is checked against its expected type first, before its
arguments, only when that type mentions `?` (`Any` or `unk`,
`GradualTyping.mentions_unknown`): that is what lets
`cons 1 (cons true nil) : list Any` check `true` at `Any`. Otherwise the
arguments come first, as in Rocq, so terms without `Any` elaborate as in
Rocq. A type that only computes to the expected one once the arguments are
known, like `lia`'s proofs by reflection, needs that order, and `lia` and
`nia` work with `Gradual Typing` on (`success/gradual_static_order.v`). The
check is syntactic: an `Any` hidden behind a definition of the expected type
does not count.

Pass `-no-soma-prelude` for plain Rocq, where each part of the
Soma prelude can be imported on its own (`From Soma Require Import
Strings Lists Show.`), or `-no-prelude` to load no prelude at all, Rocq's
included (`-noinit` and `-no-soma-prelude`). The
Soma prelude is skipped under `-boot` and `-noinit`, so Corelib, Ltac2,
Stdlib and the prelude itself are built as plain CIC. The inherited Rocq
test-suite runs with `-no-soma-prelude`, and the gradual tests import
`Gradual` explicitly.

Rocq's standard library is vendored in `theories/Stdlib` (V9.2.0, see its
README) and the build installs it with the rest, so `From Stdlib Require ...`
works without flags. The kernel is 9.3.0; this tree does not record a
joint run of the two (see Versions).

The unknown type `Any` (`unknown Type`) was called `Dyn` until the commit that
renamed it; `gradual-coverage.md` and `dev/gradual-lattice/results/` predate
that and still say `Dyn`.

Outside a proof, a bare term `t.` is evaluated and printed as `Eval lazy in t.`,
so `"Hello, world!".` is a complete program. A sentence that starts with a
name and has `:=` before its final `.`, outside brackets, is a `Definition`:
`greet name := append "Hello, " name.` is
`Definition greet name := append "Hello, " name.` (`test_implicit_definition`
in `vernac/g_vernac.mlg`, `lk_kw_before_end` in `parsing/procq.ml`). Inside a
proof the same position holds a tactic, as in Rocq, so both need the explicit
command there; ssreflect's `set x := t.` is such a tactic. `Recursive` is
another spelling of `Fixpoint`, and a recursive function still needs it.

### ML expression blocks

`ml { expression }` selects an ML-style expression grammar. It elaborates
directly to ordinary Soma terms; it neither runs OCaml nor changes the kernel.
Definitions, types and proofs outside a block keep their existing syntax.

```rocq
increment : nat -> nat := ml {
  fun n -> let next = n + 1 in next
}.

from_option : option nat -> nat := ml {
  function Some n -> n | None -> 0
}.

Require Import Sandbox.
read_update (c : cell nat) : io nat := ml {
  let* n = read_cell c in
  write_cell c (n + 1);
  ret n
}.
```

Supported forms include `let x = value in body`, local function bindings
(`let f (x : nat) = body in ...`), parallel pure bindings (`let x = a and y = b
in ...`), tuple destructuring, `fun x -> body`, `function ...`, and
`match value with | pattern -> body`. A block or enclosing parentheses closes
a match; it needs no `end`. Parenthesize nested matches to delimit which match
owns the following branches, as in OCaml. Tuples, semicolon-separated lists,
applications, annotations and numeric scopes are available too.

All right-hand sides of a parallel binding see the outer scope. No generated
temporary name can capture a source variable. `let* pattern = action in body`
expands to `Soma.Sandbox.bind action (fun pattern => body)`, and
`action; body` discards the action's result with that same bind. These forms
require `Sandbox` and its `io`; a pure `let` does not perform an action.

Operators retain Soma's notation and numeric meaning: `=` is propositional
equality, `=?` is its boolean numeric test, and `nat` arithmetic remains `nat`
arithmetic. For example, `ml { -3 + 1 }%Z` uses integer arithmetic, and
`ml { N.add 3%N 4%N }` scopes individual arguments. Supported infix spellings
are `+ - * / mod`, `:: ++`, `&& ||`, and the usual comparisons. The
corresponding notation must already be available, as it must outside a block.

`soma { term }` inside an ML block embeds the full ordinary Soma grammar,
including dependent matches and custom notation. For example:
`ml { let n = soma { let k := 4 in k + 1 } in n + 1 }`.
Scoped blocks can be nested. The names `ml`, `function` and `and` are not
reserved globally; parsing uses separate entries rather than a persistent mode.
Optional arguments, imperative mutation and unrestricted `let rec` are not
introduced by this syntax. Existing cells, buffers and checked/effectful loops
retain their explicit interfaces.

`test-suite/misc/soma_ml_blocks.sh` proves representative pure results and the
exact equality of effectful blocks with their original `bind` expressions,
including capture avoidance, parallel scope and tuple patterns.

### Gradual expressions

```rocq
Definition succ_dyn (x : Any) : nat := x + 1.
Print succ_dyn.
(* succ_dyn = fun x : Any => cast Any nat x + 1 *)

Compute succ_dyn 41.     (* = 42 *)
Compute succ_dyn true.   (* = raise : nat, a runtime type error:
                            Run-time error: expected a nat, but got true : bool. *)

Definition apply3 (g : Any) : nat := g 3.
(* elaborates to: cast Any nat (cast Any (Any -> Any) g (cast nat Any 3)) *)
Compute apply3 S.        (* = 4 *)
Compute apply3 negb.     (* = raise *)

Compute 2 + unk.         (* = S (S unk) *)
Compute (unk : nat -> bool).  (* = fun _ => unk *)

Fail Definition bad : nat := true.  (* still a static error: not consistent *)
```

| Surface syntax | Meaning (paper notation) |
|---|---|
| `Any` | the unknown type `?_□` (abbreviation for `unknown Type`) |
| `unk` | the unknown term `?_A` at the expected type `A` |
| `raise` | the error `err_A` at the expected type |
| `cast A B t` | the cast `⟨B ⇐ A⟩ t` |
| `Set/Unset Gradual Typing` | turns consistency-based elaboration on or off |
| `Set Gradual Steps n` / `Unset Gradual Steps` | the budget of gradual reduction steps per command, or none |


### Rocq libraries: `Rocq Library`

A Rocq library is Rocq: Soma takes it as it is, with no definition and
nothing translated, its terms being terms that the kernel checks, that
evaluation computes and that proofs go through. `Rocq Library
"rocq-stdpp".` (or `Rocq Library "rocq-stdpp" "1.13.0".`), in any Soma
file, then `From stdpp Require Import gmap.` (`plugins/soma_rocq`, which the
Soma prelude loads). What Soma cannot take is a library compiled by another
Rocq: Soma's kernel is not theirs, so opam's compiled packages do not load.
So the sentence, in the synterp phase, compiles the library from its source
with Soma itself, once, into the project's cache, `.soma-cache/rocq`, in a
directory named after the package, its version and Soma's Corelib, and puts
its theories in the load path. The source is `opam source` of the package, from the
repository of Rocq's packages (`coq-released`, which Soma adds to its own
switch), or a directory: `Rocq Library "mylib" in "vendor/mylib".`, compiled
again when its files change. Its theories are what its dune files declare,
`(rocq.theory (name stdpp) (package rocq-stdpp))`, or else the `-Q` and
`-R` of its `_RocqProject` or `_CoqProject`. They are compiled in the order
`rocq dep` gives, by `rocq c`, as Rocq: without Soma's prelude, whose names
(`R`, the reals) and gradual typing a library does not expect. Nothing else
of the source runs. A
library that loads an OCaml plugin is refused, as a plugin is built against
the Rocq it extends. A library's dependencies are named by their own `Rocq
Library`, before it. `examples/example_projects/rocq_stdpp` keeps a shop's
stock in std++'s finite maps, computed by Soma and proved with std++'s
lemmas.

### C modules: `.definition` next to `.c`

The C binding mechanism is already available to executables and Sandbox
images. A binding declares how to call a native operation; it does not supply
the operation itself. For example, running a second guest program needs native
CPU context entry, trap vectors and page-table operations. Those belong in a
small architecture-specific C/assembly library, exposed through `.definition`
handles and `word64` values. An application's loader, scheduler and syscall
policy can remain Soma. No OCaml policy wrapper is required for that boundary.

A C file `FILE.c` is used through `FILE.definition`, next to it, as an
OCaml module is, and is plain C: Soma writes the OCaml that calls it
(`vernac/somaC.ml`), and `FILE.soma.h`, the declarations of the functions
FILE.c defines, which it includes. Each declaration is the C function
`FILE_name`, its type made of:

| Declared | In C |
| --- | --- |
| `int`, `nat` | `int64_t` (a negative result given as a `nat` is `0`) |
| `word64` (Soma.Word64's) | `uint64_t` |
| `bool`, `float` | `bool`, `double` |
| `buffer` (Sandbox's), as an argument | `soma_bytes { uint8_t *ptr; size_t len; }`, which C may read and write in place, valid during the call; C never gives one |
| `string`, as an argument | `soma_str { const uint8_t *ptr; size_t len; }`, valid during the call |
| `string`, as the result | the function returns `void` and fills its last argument, `soma_buf *out`, with bytes from `malloc`, which Soma copies and frees |
| a type the definition declares (`ctx : Type.`) | `soma_handle`, an `uintptr_t` Soma keeps and gives back, never looks into |
| `unit`, as the only argument, or the result | no parameters, `void` |
| `option A`, as the result | the function returns whether there is one, and writes it to its last argument, `A *out` |

```
(* machine.definition, next to machine.c *)
buffer : Type.
buffer_new : nat -> buffer.
buffer_get : buffer -> nat -> option int.
ticks : unit -> int.
```

```c
#include "machine.soma.h"
bool machine_buffer_get(soma_handle h, int64_t i, int64_t *out) { ... }
int64_t machine_ticks(void) { uint64_t t; __asm__ volatile("mrs %0, cntvct_el0" : "=r"(t)); return t >> 1; }
```

A declaration C cannot take (a list, a product, a function, a type with
parameters, a declaration in a submodule, a library) is refused when the
definition is compiled, saying what C takes. The C file is compiled
against the header, so a function whose type is not its declaration's is
a C compiler error (`conflicting types`) when the program is built; an
image's C is also checked so by `soma build --no-image`, with the
machine's C compiler.

An executable links FILE.c (dune's `foreign_stubs`). A Sandbox image
builds it for Solo5, in a library of its own (`soma_c`, in the image's
project, which a program with C modules has to itself: `-c` in its name):
freestanding C, with the string functions and `malloc` of Solo5's libc,
no stdio or threads, and assembly where C has none. A page cannot call C.

A C function that does something (allocates, writes memory, reads a
clock) is called when OCaml evaluates it: in an executable, at the point
the extracted code reaches it, in OCaml's order within an expression. In
an image, Sandbox's `call f` calls `f tt` in order with the other actions:
`x <- call (fun _ => buffer_get b 3) ;; ...`, `t <- call ticks ;; ...`.
`examples/example_projects/c_arith` is an executable calling C with each
kind of argument; `examples/example_projects/c_image` fills a C buffer and
reads the ARM counter with inline assembly in a unikernel;
`test-suite/misc/soma_c.sh` builds both, more than five arguments, and the
refusals. Not yet: callbacks from C into Soma, structures by value, a
prebuilt C library, handles freed by the collector.

### Theorems proved in Lean: `.definition` next to `.lean`

`FILE.definition` next to `FILE.lean` declares theorems that the Lean file
proves about Soma's definitions, `name : statement.`
(`theories/Soma/Lean.v`, `plugins/soma_lean`). `Lean Bind`, at its end,
checks them with Lean before Soma takes them:

1. Soma translates the definitions that the statements use into a Lean
   module `Soma` (`def Soma.series.fib ...`), which `FILE.lean` imports.
2. `FILE.lean` is compiled, by the Lean of the project's `lean-toolchain`.
3. Each translated statement must be the type of its theorem
   (`example : STATEMENT := @name`).
4. A theorem that depends on `sorryAx` (`#print axioms`) is refused.

What is translated is a fragment: `nat`, `bool`, lists, pairs and options,
their functions and comparisons, the connectives and quantifiers, `match`,
and structural `Fixpoint`s, a variable matched being written as its pattern
in its branch so that Lean sees the recursion is structural. The rest is
refused, saying what. To Soma's kernel, a theorem is an axiom, trusted as
Lean's kernel, the axioms Lean's proof uses, and the translation are, which
`soma explore` lists. `test-suite/misc/soma_lean.sh` tests it, and is
skipped without Lean.

### Run-time errors

A cast that fails reduces to `raise`, which keeps nothing but its type, and
`raise` only spreads to what looks inside it: `append "Hello, " raise` is
the string `"Hello, "` ending in `raise`. A term evaluated (`Compute`,
`Eval`, a bare term) whose value has a `raise` in it is printed as far as
it was computed, followed by what went wrong:

```rocq
greet_any (name : Any) := append "Hello, " name.
greet_any 42.
(*   = "Hello, " ++ raise
     : string
Run-time error: expected a string, but got 42 : nat. *)
```

The kernel records each cast that fails on its own (rather than on a
`raise` it was given): the type expected, the type of the value, and the
value (`Gradual.failures`, `kernel/gradual.ml`), and `vernac/gradualErrors.ml`
words them:

| What failed | Message |
|---|---|
| different types | `expected a string, but got 42 : nat` |
| a function where data is expected | `expected a nat, but got a function of type nat -> nat` |
| the same family at other indices | `expected a proof of 1 = 2, but got a proof of 1 = 1`, `expected a Vector.t nat 3, but got a Vector.t nat 2` |
| a value under a binder | `expected a string, but got a nat` |
| a `raise` of the program | `raise in safe_div (file.soma:12)`: the definitions the term uses that raise |

A string that ends in `raise` prints as `"Hello, " ++ raise` rather than as
its characters (`Register ... as soma.string.append`, in
`Soma.Strings`). `soma run` fails when the program's last value is a
run-time error. Compiled code raises `Gradual_rt.Cast_error` at the cast
instead, worded the same way from the types it has at run time
(`expected a bool, but got a nat`, without the value); a MirageOS image
prints it as `Run-time error: ...` and exits. An error that reaches a
`match` whose type cannot hold it (a `string`, which is OCaml's `char
list`) is raised as it is, saying what it was, and not only where it
ended up.

### What an `Any` may be

When a definition is declared, each cast from `Any` to a type `T` in it
is looked at (`GradualTyping.casts_that_may_fail`, warned about in
`vernac/declare.ml`): the value is followed back, through `match`es,
`let`s and the definitions it calls, to the casts that made it an `Any`,
which give the types it may have been made from. Each of those that is
not consistent with `T` is a run-time error whenever the value is one,
and is reported, with the definition where it was made an `Any`:

```
Warning:
respond: start_of request is an Any that may be
a string (made an Any in start_of), and it is used as an N. A string is never
an N: where it is one, this is a run-time error, "expected an N,
but got a string". It may also be an N (made an Any in start_of), which is
fine. [gradual-may-fail,vernacular,default]
```

A value whose origin is not known, an argument of type `Any`, `?`, what
a recursive function computes, is not reported. A theorem whose subject
is such a cast gets the warning too: it holds for the [raise] the cast
is, and so says nothing for those values.
`examples/example_projects/unchecked_counter` is `counter_server`
without its parser, where the warning shows the counter failing for
every count in a request; `test-suite/misc/soma_may_fail.sh` tests it.

### Exploring a program: `Explore`

`Soma.Explore` (`theories/Soma/Explore.v`, not in the prelude) describes
a program as a state machine, a `model`: the inputs to try (a scope, as
in Alloy), the state each starts in, the actions and what each does, a
depth, invariants of states and properties of steps, each a named
`bool`-valued function. `Explore model.` (`plugins/soma_explore`) tries
them as TLC does a TLA+ specification: from each input, each sequence of
actions up to the depth, breadth first, not exploring again a state
reached before from the same input. States and properties are evaluated
as `Eval` evaluates a term, so a run-time error, a cast that failed, is
found as a violation is, with its message. Each violation is reported
with its input and the behaviour up to it (the actions and the states
after them), and the command fails; without one, it says what was
explored. `examples/example_projects/counter_server/model.soma` and
`unchecked_counter/model.soma` are examples; `test-suite/misc/soma_explore.sh`
tests it.

`soma explore FILE` checks FILE in a temporary directory, as `soma run`
does, without an image, and then reviews it with the project files it
imports (the command `Review`, in the same plugin):

- Models: every `Soma.Explore.model` defined is explored (its `Explore`
  commands, during a review, are left to the review).
- Escape hatches, where static types are given up: each definition whose
  type has `Any`, what its casts make an `Any` from and use one as, and
  its `?` and `raise`.
- Issues, where a guarantee does not hold: the casts that may fail (as
  `gradual-may-fail` says), a theorem whose statement has one, what is
  assumed (an `Axiom`, a `Parameter`, an `Admitted` proof) and what rests
  on it, and a proof whose evidence is a gradual primitive.
- What `main` does outside the program, for a Sandbox program: `print`,
  `serve (port 8080)`, `fetch`, ...

It fails when a model has a violation or there is an issue; escape
hatches alone are gradual code doing what it says.

### Cryptography: `Crypto`

`Soma.Crypto` (`theories/Soma/Crypto.v`, not in the prelude: `Require
Import Crypto.`) is SHA-256 (FIPS 180-4) and RSA signatures (PKCS #1
v1.5 of a SHA-256 digest), written in Soma on Rocq's primitive 63-bit
integers:

```rocq
Require Import Crypto.
id : string := Crypto.sha256 "abc".   (* "ba7816bf...f20015ad", lowercase hex *)
ok : bool := rsa_verify 256 n e "message" signature.
```

- `sha256 : string -> string` is the hex digest. `sha256_bytes` gives its
  32 bytes (`list int`, each below 256). `sha256_of_bytes` hashes bytes
  rather than a string's characters. `sha256_concat` hashes strings one
  after the other without joining them.
- `rsa_verify k n e msg sg` and `rsa_sign k p q dp dq qinv msg` work on
  big-endian bytes (`k` is the key's size in bytes). Signing uses the
  Chinese remainder theorem. Both produce Cryptokit's bytes (`RSA.sign_CRT`
  of the EMSA, `RSA.unwrap_signature`). `bytes_of_hex`, `hex_of_bytes`,
  `bytes_of_string` and `string_of_bytes` convert.
- The kernel computes them (`vm_compute`). `Crypto.v` checks FIPS 180-4's
  vectors, and a 512-bit Cryptokit key's signature verified and made
  again, as `Example`s, so a proof may compute a digest or a signature.
- They need no library, so a binary and a Sandbox image run the same
  code. Extraction makes the integers OCaml's ints: a generated
  `uint63.ml`, the kernel's `Uint63`, next to `float64.ml`. JavaScript's
  ints have 32 bits, so a page would compute them wrong.
- A message is read one byte at a time in tail calls, so its length is
  not bounded by the stack.
- Extracted, SHA-256 hashes about 20 MB/s, roughly a tenth of C's speed.
  A 2048-bit signature takes about 12 ms. Verifying takes about 1 ms with
  e = 65537, or 90 ms with a 2048-bit public exponent such as Cryptokit's
  `RSA.new_key` picks. Numbers are lists of 31-bit limbs, multiplied by
  Montgomery's method.
- `test-suite/misc/soma_crypto.sh` checks SHA-256 against the system's
  `sha256sum` up to 14 MB, and RSA against a 2048-bit Cryptokit key's
  signatures.

`theories/Soma/CryptoSpec.v` gives a mathematical integer interpretation of
the actual 31-bit limb lists. It proves `add_carry1`, `add_carry`,
`mul_limb`, and `mul_big` preserve their arithmetic meaning and limb bounds,
and that trimming high zeros preserves value. These results use Rocq's
primitive Uint63 specifications. `soma_crypto_arithmetic.sh` checks the
extracted operations against Zarith, including carry boundaries and large
deterministic random operands. Byte/limb encoding, Montgomery reduction,
SHA-256, full RSA correctness and key-generation primality remain separate
proof obligations; these arithmetic results do not establish cryptographic
hardness or side-channel security.

### The machine's host: `Host`

`Soma.Host` (`theories/Soma/Host.v`, not in the prelude: `Require
Soma.Host.`) is what a program built for the machine asks of the system
it runs on, as Sandbox's `io` is what an image asks of its hypervisor:
its arguments and output, the clock, files, paths, the environment,
processes and TCP sockets, each one primitive:

```rocq
Require Soma.Host.

main : unit := Host.print_lines ("hello" :: Host.argv tt).
```

- Each is a parameter that Soma never computes, neither the kernel nor
  the evaluation of a term, so no proof holds by running the machine,
  and `soma explore` lists the ones a program uses ("Soma.Host's
  primitive").
- Soma carries them out: a program whose `main` uses one is built as one
  that uses an OCaml module is (see "OCaml modules"), with Soma's own
  runtime for them (`toplevel/somaHost.ml`, written as `soma_host.ml`
  next to the extracted program and checked against Host.v's
  declarations), which uses OCaml's Unix, a library that comes with the
  compiler. The program has no OCaml of its own. That runtime needs OCaml
  5.1 or later: the switch Soma makes has the newest, and a program over
  Host in a `$SOMA_OCAML_SWITCH` with an older OCaml is refused, saying so
  (`test-suite/misc/soma_host_ocaml_version.sh`).
- Most answer with `(carried out or the boolean read, (a number, data))`,
  the data strings; numbers given are decimal text. Descriptors (sockets,
  and the pipe a process writes its output on) are known by names the
  host gives them. A program decides what each answer means: Pantheon's
  node turns its operations into them, one primitive each.
- `test-suite/misc/soma_host.sh` builds a program over them and checks
  its arguments, files, a process's output and a socket's bytes.

`theories/Soma/HostSpec.v` specifies partial-write byte accounting.
`advance_preserves_bytes` and `writes_preserve_bytes` show that accepted
write counts and retries preserve the original bytes across arbitrary
finite traces. Counts beyond the pending buffer are refused. The
`soma_host_partial_writes.sh` test uses this proved advancement function
with the actual Unix socket shim under forced partial writes and
backpressure, checking every received byte. Delivery, syscall behavior,
process semantics and file durability remain host contracts, not conclusions
of these accounting theorems.

## Architecture

The kernel stays the CIC kernel. The cast calculus (CastCIC) is encoded with
three **axioms** that the kernel knows about through its *retroknowledge*,
the same mechanism used for primitive integers:

```rocq
Universe gradual.
Axiom unknown : forall A : Type@{gradual}, A.
Axiom err     : forall A : Type@{gradual}, A.
Axiom cast    : forall A B : Type@{gradual}, A -> B.
Register unknown as kernel.gradual_unknown.
Register err     as kernel.gradual_err.
Register cast    as kernel.gradual_cast.
```

**Typing is unchanged**: these are ordinary axioms. Only **reduction**
changes, and only for terms headed by these constants. That is why the
static fragment behaves exactly as in CIC (conservativity), and why
`Print Assumptions` lists the axioms whenever a development uses gradual
features. (The theory is deliberately inconsistent: `unk : False`.)

So that proofs stay proofs, saving a proof (`Qed`, `Defined`) reports
(`gradual-proof`) a proof whose evidence is a gradual primitive: `unknown
P`, `err P` or `cast A P v` for a proposition `P` (`unk`, `raise`, a cast to
the statement), which inhabits any statement. It is looked for in the
proof and in the transparent bodies of what it uses, so a fake hidden in a
definition (`cheat : 1 = 2 := raise`) or in data (`exist _ 3 raise`, a
"proof" that 3 is even) is found too (`GradualTyping.proof_fake_evidence`).
The same primitives at other types (`cast nat Any n`, `Any`) are the
gradual program a theorem is about, and are not evidence: theorems about
gradual programs, such as `forall n, succ_dyn n = n + 1`, and theorems
about records with fields of type `Any` are not reported. A fake that
occurs in the statement itself is its subject, and is not reported either.
In `.exp` files this is an error (`theories/Soma/Proof.v`); in Rocq's
`.v` files, a warning:

```rocq
Lemma by_hidden : 1 = 2. Proof. exact hidden. Qed.   (* hidden : 1 = 2 := raise *)
(* Warning: by_hidden: raise (in hidden) stands in for a proof of (1 = 2),
   so the theorem is not proved (see Print Assumptions). *)
```

### Reduction rules (`kernel/gradual.ml`)

`A`, `B` are in weak head normal form. "Germ-free": a value of type `?` is
`cast A Any t`, where `A` is the original head type.

| Redex | Reduct |
|---|---|
| `unknown (forall x:A, B)` | `fun x:A => unknown B` (same for `err`) |
| `match unknown (I pars idx) return P with … end` | `unknown (P idx (unknown (I pars idx)))` (same for `err`) |
| `fix f … (unknown I) …` | unfolds, like a constructor (then hits the rule above) |
| `(unknown R).(p)` (primitive projection) | `unknown (type of p)` |
| `cast A A t` (syntactically equal) | `t` |
| `cast (err _) B t`, `cast A (err _) t` | `err B` |
| `cast Any Any t` | `t` |
| `cast Any B (cast A Any t)` | `cast A B t` |
| `cast A Any (unknown _)` / `cast Any B (unknown _)` | `unknown B` (same for `err`) |
| `cast (forall x:A1, B1) (forall x:A2, B2) f` | `fun x:A2 => cast B1[x'/x] B2 (f x')` where `x' := cast A2 A1 x` |
| `cast (Sort s1) (Sort s2) T` | `T` if `s1 ≤ s2` in the universe graph, else `err` (stuck on universe variables the environment does not know) |
| `cast (I p1) (I p2) (c p1 args)` | `c p2 (cast Tᵢ[p1] Tᵢ[p2] argsᵢ)` |
| `cast (I p1 i1) (I p2 i2) (c …)` (indexed) | as above, if the indices the constructor produces are compatible with `i2` (`?` matches anything), else `err` |
| `cast (I …) (I …) (unknown _)` | `unknown B` (same for `err`) |
| `cast (array A1) (array A2) t`, `A1 ≢ A2` | stuck (array elements are not cast) |
| any other head clash among Π / Sort / inductive / primitive type (`int`, `float`, `string`, `array`) | `err B` |
| anything involving a neutral type | stuck |

The GCIC^G decision is in the injection rule `cast A Any t`. It keeps `A`
as is and never lowers the universe of a Π germ, so `Any -> Any : Type@{i}`
whenever `Any : Type@{i}`.

### Where the rules are hooked

| Component | File | Used by |
|---|---|---|
| kernel lazy machine | `kernel/cClosure.ml` (`knr_gradual`) | kernel conversion, `lazy`, `rocqchk` |
| pretyping machine | `pretyping/reductionops.ml` (`gradual_step`) | unification, `whd_all` |
| call-by-value | `pretyping/cbv.ml` (`cbv_gradual`) | `cbv`, `compute`, and `vm_compute`/`Compute` in gradual mode |
| simpl / hnf | `pretyping/tacred.ml` | `simpl`, `hnf` |
| cbn | `tactics/cbn.ml` | `cbn` |
| registration | `kernel/retroknowledge.ml`, `safe_typing.ml`, `vernacentries.ml`, `checker/` | `Register … as kernel.gradual_*`, `.vo` validation |
| extraction | `plugins/extraction/extraction.ml` (`extract_gradual`), `gradual_rt.ml` | OCaml extraction, with casts checked at run time |

### Elaboration (`pretyping/gradualTyping.ml`)

GCIC elaboration replaces conversion by **consistency**: equality up to `?`.
It plugs into Rocq's coercion mechanism (`pretyping/coercion.ml`) as the
last resort, after unification and ordinary coercions have failed:

- a term `t : A` where `B` is expected, with `A ~ B` consistent, becomes `cast A B t`.
  Evars are instantiated where the two types agree, so for
  `vcons 1 (vcons true vnil) : vec Any unk` the parameter is set to `Any`
  although `S ?n` and `unk` do not unify;
- a term `f : Any` in function position becomes `cast Any (Any -> Any) f`;
- a term `T : Any` in type position becomes `cast Any Type T`;
- in a cast between `Any` and an inductive type, arguments that nothing
  determines are `?`: `snd p` with `p : Any` casts `p` to `Any * bool`;
- the condition of an `if` of type `Any` is cast to `bool`.

### Recursion through `Any`

Rocq accepts a `Fixpoint` only if its recursion is structural, checked by
the guard condition. GCIC^G gives up termination, and recursion through
`Any` has no structure to check: an argument of type `Any` (`fact (n : Any)`),
or a constructor argument made `Any` (`Plus (a : Any) …`, then `eval a`).
Under Gradual Typing, a block of fixpoints that uses the gradual primitives
and fails the guard is therefore accepted without checking it, with a
`gradual-unguarded-fixpoint` warning:

```rocq
Fixpoint fact (n : Any) : nat := match n with O => 1 | S k => n * fact k end.
(* Warning: fact: not structurally recursive; it recurses through gradual
   types, so its guard is not checked (gradual typing gives up termination). *)
Eval lazy in fact 5.      (* = 120 *)
Print Assumptions fact.   (* fact is assumed to be guarded. *)
```

- The recursive argument is the first possible one of type `Any`, or the
  first possible one. A fixpoint unfolds on `?`, `err` and the values of
  `Any` (injections `cast A Any t`), in every reduction machine.
- These unfoldings count towards `Gradual Steps`, so a loop through `Any`
  stops with the step error.
- Fixpoints without gradual primitives are checked as usual.
- The kernel accepts a fixpoint whose recursive argument has type `Any`
  only without guard checking and without VM and native compilation
  (`kernel/inductive.ml`). The declaration sets both, and gradual terms
  never run on the VM (`vm_compute` falls back to `cbv`). Any other
  non-inductive recursive argument is still rejected (bug 15621).

`dev/gradual-lattice/` measures these rules on typed programs whose
annotations are made less precise: see its README.

## Extraction to OCaml

`theories/Soma/NativeSpec.v` gives signed-word contracts for the native
`nat` arithmetic mappings: addition and multiplication agree with natural
arithmetic when the result fits, and subtraction agrees with truncated
subtraction for valid nonnegative operands. It also proves guards that can
be checked without first overflowing. These are conditional results, not a
proof of any program's range invariants. `soma_native_contracts.sh` checks
the actual extracted operations and byte-string mappings at boundaries,
including deliberate overflow counterexamples to unconditional equivalence.

`theories/Soma/Word64.v` adds `word64`, unsigned 64-bit words: registers,
addresses, page-table entries, exception syndromes, which a 63-bit `int`
cannot hold. In the kernel a word is a binary `N` below 2^64 with that
proof, and each operation is defined on `N` and reduced modulo 2^64, so
the definitions are the specification: `add`, `sub`, `mul` and `neg`
wrap; `divu a 0` is `0` and `remu a 0` is `a`; a shift count is taken
modulo 64, as AArch64's are; `ltb` and `leb` compare unsigned, `slt` and
`sle` two's complement; `bits w lo width` is a field (`bits esr 26 6`, an
exception class); `to_hex`, and conversions to and from `N`, `nat` and
`PrimInt63.int`. `to_N_inj` says words are equal when their numbers are,
and `eqb_spec`, `add_comm`, `add_zero`, `sub_self` and `ltb_spec` are
proved from it. Compiled (an image or an executable), a word is OCaml's
`int64` and each operation the `Int64` function with the same meaning
(`word64_extraction` in `toplevel/somaMirage.ml`), as `nat` is OCaml's
`int`: what the compiled code is trusted to compute.
`examples/example_files/mirage_word64` computes 26 cases (wrapping,
division by zero, signed and unsigned comparison, shifts of 64 and 65,
fields, conversions) in an image, which compares them with a list its
`.exp` proves is what the kernel computes; `dev/mirage-check.sh` boots
it, and `test-suite/misc/soma_word64.sh` checks the extraction, that a
wrong expectation is refused, and a C module that rotates a word.

`theories/Soma/CastSpec.v` checks conversion laws for the actual gradual
primitives on naturals, booleans, strings, lists, options, pairs and
functions. It also specifies projections whose dynamic tag changes at run
time. These proofs use the existing gradual kernel primitives; they are
not a general simulation theorem for extraction. `soma_cast_contracts.sh`
checks the corresponding extracted paths, including higher-order wrappers
and distinct `Cast_error` and `Unknown_term` failures.

`test-suite/misc/soma_contract_assumptions.sh` audits the theorem assumption
sets. Native arithmetic, Wire, socket accounting and storage protocol
contracts must be closed under the global context. Crypto contracts may
use only the listed existing Uint63 primitives/specifications; cast laws
may use only `Gradual.cast`, `Gradual.unknown` and `Gradual.err`. Any other
global assumption fails the audit. These contracts and conformance tests
strengthen the execution boundary; they do not amount to a verified OCaml
compiler, OS, cryptographic implementation, or end-to-end Pantheon proof.

Extraction erases types, which casts need. So OCaml extraction compiles
each `cast A B t` to a call to a small runtime, `Gradual_rt`
(`plugins/extraction/gradual_rt.ml`), with runtime descriptions of `A`
and `B`. The runtime applies the rules above. The extracted file embeds the
runtime: it only needs the OCaml standard library, so it also builds for
MirageOS unikernels.

```rocq
Definition succ_dyn (x : Any) : nat := x + 1.
Extraction succ_dyn.
(* let succ_dyn x =
     add (Gradual_rt.cast_with ... Gradual_rt.unknown_ty
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil) x)
       (succ 0) *)
```

- A value of type `Any` is the value plus the description of its type.
- A cast between function types wraps the function. The wrapper makes a
  tail call when the codomain needs no cast, so Ω loops in constant stack.
- For each inductive type, extraction generates a match on its
  constructors that casts their arguments and checks the indices. It
  therefore works with `Extract Inductive` (e.g. `nat => int`).
- **`?` and `err` are values**, as in the kernel, at inductive types
  extracted as OCaml variants or records. `cons raise nil` is a list of
  length 1, `2 + unk` is `S (S unk)`, and a cast that fails inside data
  gives `raise` there. They are blocks with a reserved tag (245). Every
  `match` of a file that uses the runtime goes through
  `Gradual_rt.check`, which raises `Gradual_rt.Cast_error` or
  `Gradual_rt.Unknown_term` when such a value is eliminated. The extracted
  `.mli` exports these exceptions together with `check`, `force` (raises if
  `?` or `err` occurs anywhere in a value's data) and
  `is_unknown`/`is_error`. OCaml code that receives extracted values must
  use them before matching on values that may contain `?` or `err`:
  matching on them directly is undefined behavior in OCaml.
- **Type parameters** that casts need are passed at run time. A parameter
  is needed when it occurs in the types of a cast, `unknown` or `err`, or in
  an argument for a needed parameter of another function, including
  recursive calls. The constant then takes the type's description as an
  argument and its callers pass it:

  ```rocq
  Definition to_dyn {A : Type} (x : A) : Any := x.
  (* val to_dyn : __ -> 'a1 -> __
     let to_dyn a x = Gradual_rt.cast_with ... a Gradual_rt.unknown_ty x *)
  ```

  Other type parameters are erased as usual, so code without casts is
  extracted as before.
- The test is `test-suite/misc/gradual_extraction.sh`. Each result must
  print as the kernel's value, or be marked with the documented difference
  that explains it. The MirageOS on Apple Silicon test matrix runs the same
  program as an `hvt` unikernel.

Extraction differs from the kernel in these ways:

- **Modular gradual output uses one shared OCaml runtime.**
  `Separate Extraction`, `Extraction Library` and `Recursive Extraction
  Library` write `soma_gradual_rt.ml` beside their output. Compile and link
  that unit before the extracted modules. Unknown/error markers, exceptions
  and constructor-cast registrations are shared, and cast-free consumers
  guard their eliminations too. Monolithic `Extraction "file" ...` remains
  self-contained. Runtime-free modular output needs no runtime unit.
- **Gradual modules must use the same runtime ABI.** Previously extracted
  runtime-free modules or modules with a private embedded runtime cannot be
  mixed into shared gradual output. The generated dependency check rejects
  a missing ABI at OCaml compilation, or a different runtime at module
  initialization. Re-extract the complete dependency closure with
  `Separate Extraction` or `Recursive Extraction Library` to recover.
  An unrelated `soma_gradual_rt.ml` is never overwritten.
- **Functor result types have application-aware runtime identities.**
  Exported physical brands agree inside and outside one application,
  propagate through aliases and module arguments, and distinguish separate
  applications, even when their arguments are the same. Constructor casts
  also check the extracted representation fingerprint; incompatible custom
  representations fail closed. These identities are process-local runtime
  metadata, not a serialization format. The kernel checks are unchanged.
- **Only the type parameters of constants are passed.** A cast at a type
  variable bound elsewhere (a local `fun (A : Type) => …`, a type stored in
  a constructor) is rejected at extraction time. So is a function that
  needs type parameters at run time used without them, for example
  `@to_dyn` passed to a function expecting `forall A, A -> Any`: the
  callee would not pass the description.
- **Eliminating `?` or `err` propagates them only when the type of the
  `match` has a runtime description.** As in the kernel, a `match` on them is
  `?` or `err` at its type: `unk + 2` is `unk`. Extraction compiles such a
  `match` to `if Gradual_rt.is_exc_value x then Gradual_rt.propagate ty x
  else match x with …`. The type's description is only built when `x` is
  `?` or `err`, and the test needs no allocation or C call. When the type of
  the `match` has no runtime description (it mentions a type variable that
  is not passed), or cannot hold the value (see below), eliminating `?` or
  `err` raises `Unknown_term` or `Cast_error`.
- **Types that cannot hold them raise at once.** This covers types mapped
  to an OCaml type by `Extract Inductive` (`nat => int`, `bool => bool`),
  singleton and coinductive types, and types with more than 244
  constructors with arguments. A cast that fails at such a type, or `?`
  at it, raises immediately, also inside data.
- **Universe levels are erased.** The runtime compares only Prop, Set
  and Type, where the kernel asks the universe graph.
- **Proofs are erased**, so casts between propositions are not checked.
- **Coinductive types** are not supported in casts yet. The kernel would
  have to rebuild a constructor of a `cofix` without unfolding it more than
  once, and the runtime would have to keep the rebuilt value lazy.
- **Primitive types** follow the kernel. Equal ones cast to themselves and
  clashes give `err`. Their values are OCaml values (e.g. `int` through
  `Extract Inlined Constant`), so `?` and `err` at them raise at once.
  Casts between arrays of different element types raise
  `Cast_error`; the kernel leaves them stuck.
- Only OCaml is supported. Haskell and Scheme extraction print an error.

## Sandbox: programs as unikernels

Sandbox changes can be checked on Linux with `soma build --no-image FILE.soma`.
With `SOMA_MIRAGE_SWITCH` unset or empty, builds also take this path. Soma
extracts the program and generates the Mirage project in `$SOMA_MIRAGE_DIR`
(or `$XDG_CACHE_HOME/soma/mirage`, otherwise `~/.cache/soma/mirage`), then
checks its OCaml with abstract stand-in interfaces, including the network
functor. The generated `config.ml` is parsed with that compiler
(`ocamlc -stop-after parsing`): it is Mirage's configuration DSL, and the
stand-ins do not include the `Mirage` module. No image is built or run.
`dev/mirage-check.sh --no-image` runs this on the Sandbox examples and on a
program that misuses an `io` result, with no solo5 and no Mirage switch.
With the switch set and without `--no-image`, the image build is unchanged.
Each stand-in is a subset of its library's real interface, with the same
labels and optional arguments; `toplevel/somaMirage.ml` (`standins_mli`)
names the library and file it comes from, and
`test-suite/misc/soma_no_image_signatures.sh` checks code the real ones
accept and refuse. What it cannot check is linking (a missing package in
`config.ml`, a C stub) and what the image does when it runs.
`elapsed_ms start finish : N` subtracts two monotonic readings (saturating
at zero if reversed). Milliseconds use binary `N`, including at the runtime
boundary, so timestamps do not allocate unary naturals. The example
`examples/example_files/mirage_milliseconds/mirage_milliseconds.soma` measures
a 1000 ms sleep; `dev/mirage-check.sh` builds and boots it alongside the
existing images. `test-suite/misc/soma_milliseconds.sh` checks extraction
and rejects a reading used as a `nat`, without sleeping.

`examples/example_files/mirage_raw_link/mirage_raw_link.soma` is a server
that prints its `local_address` and echoes raw chunks, and, given an
address, its own client, which sends `"abc"` without a line break and
expects the echo, then the server's `"idle"` after its `receive` times out;
`dev/mirage-check.sh` boots both (from the Mac, a terminal without macOS's
Local Network permission cannot reach the image: `No route to host`).

Checked TCP operations preserve Mirage's diagnostic reason, rather than
translating it into an operating-system errno. This lets a Linux personality
choose its own errno policy. The older `send`, `send_buffer`, `receive`,
line/frame readers and mailbox events keep their existing types and treat
transport failures as closure. After a checked failure closes a link, later
operations see a closed link. Orderly `TcpEof` ends reading but leaves writing
available; use `close` when finished. Legacy `receive` still closes at EOF.
A timed-out read retains both arriving data and
its eventual terminal error until the next read observes them. Cancelling an
individual reader (for example, the losing side of `race`) also leaves the
connection's in-flight read intact. Closing the connection is explicit and
separate from cancelling a wait.
`examples/example_files/mirage_tcp_errors` distinguishes an orderly close from
a reset. `test-suite/misc/soma_tcp_errors.sh` checks the generated interfaces
and, with host Lwt or `LWT_SOURCE` pointing at a vendored `lwt/src/core`, exercises
the actual generated TCP adapter with controlled real Lwt promises.
On Solo5/Mac, `SOMA_MIRAGE_SWITCH=kykeon python3 dev/tcp-errors-check.py`
builds and boots a guest against local orderly-close and TCP-reset fixtures,
including a write after read EOF; it makes no model requests.
Real peer-reset detection requires a stack that reports resets: upstream
`tcpip` 9.0.1 collapses them into EOF. The rococompute Mirage/Mac overlay's
`tcpip.9.0.1+hvf.1` preserves the reset reason. Update that overlay and re-lock
existing Mirage projects to adopt it; an already cached dependency tree retains
its locked stack version. The checked API preserves whichever errors its
underlying stack supplies.

A disk is named by a string literal (`disk_read "rootfs" 0 8`): the image
declares a block device for each name the program uses (MirageOS's
`block_of_file`), so a name computed at run time is refused when the
program is built, saying so. Names are 1 to 31 letters and digits, and not
`storage`, the named files' device. `soma run` attaches `NAME.img`, or
the file `--disk=NAME=FILE` gives; run by hand, it is `solo5-hvt
--block:NAME=FILE`. The project of an image with
disks is named after them (`plain-disk-data`), each set of disks its own.
`examples/example_files/mirage_disk/mirage_disk.soma` reads a disk's
geometry and first sector, copies it to the next, and checks that a read
past the end and a partial-sector write are refused; `dev/mirage-check.sh`
boots it on a 64-sector disk and checks the copy reached the file.

`examples/example_files/mirage_await/mirage_await.soma` forks three tasks
and adds up their results, awaits one that fails for its reason, and one
that is slow, first for 10 milliseconds; `dev/mirage-check.sh` boots it.
`examples/example_files/mirage_tasks/mirage_tasks.soma` spawns three tasks
that add to one cell and count themselves done in another, and one that
fails; `dev/mirage-check.sh` boots it, and checks the total and that the
failure was reported while the others went on.

`loop step initial : io A` runs a returning state machine. Each step returns
`Continue next_state` to run again or `Finish value` to return the result.
State and result types can differ. Unlike the existing never-ending
`iterate`, it can implement an interpreter that advances through work and
then returns a command's result. There is no implicit iteration quota,
termination assumption, yield or fork. The step's own effects provide any
waits and cooperative cancellation. Failures stop the loop and keep their
original identity; catch/finally scopes work around the whole loop.

`examples/example_files/mirage_loop` checks a 100,000-step loop, context,
failure and cancellation. `test-suite/misc/soma_loop.sh` executes the emitted
runtime with real Lwt, checks a million immediate steps, early finish, native
result identity, pending work, exception boundaries and state/closure
collection; `SOMA_TEST_HVF=1` adds the Solo5 example. This is runtime support
for unrestricted effectful iteration, not a proof that a user's step
terminates or that the native loop implements a formally verified semantics.

`examples/example_files/mirage_async_control` checks cooperative cancellation,
cleanup on failure and cancellation, races, and task-local context across waits.
`attempt body` recovers a failure in the same task as `TaskFailed`; an explicit
`exit` still exits the image. `finally body cleanup` always runs cleanup when
an action finishes, fails or is cooperatively cancelled. A cleanup failure
replaces the original result. `race left right` returns the first result as
`awaited A` and cancels the other action; use a sum type to distinguish sides.
Cancellation is cooperative: a foreign promise made with `Lwt.wait` cannot
be cancelled. `yield` gives other ready tasks a turn without a timer.

`catch body recover` executes `body` and gives `recover` the original
`exception_value` if execution fails. It preserves native exception identity,
payloads and dynamic task context, including for a promise rejected later.
Cancellation is recoverable too. An explicit `exit` bypasses the handler.
`throw_exception error` rejects with that same exception object; a handler's
own failure escapes its catch. This uses the current backend's `Lwt.catch`
boundary, including its distinction between a handler throwing synchronously
and returning a rejected promise. Native resource-exhaustion exceptions that
Lwt excludes from recovery remain excluded.

`new_failure message` allocates a native `Failure` exception without raising
it. `same_exception a b` compares object identity, and `exception_message e`
returns `Printexc.to_string e` for diagnostics. Native `.definition`
signatures can accept or return `exception_value` (the backend's `exn`),
so classifiers can recognize their actual exception constructors without
string parsing. The handle has no numeric ID and is garbage-collected.
`ExceptionValue n` and matching the handle to obtain a number fail.
`attempt` retains its existing string-based `TaskFailed` interface; use
`catch` when identity, classification or rethrow matters. Keep native effectful
calls inside `call`: catch protects execution of the action, not its earlier
construction. `finally` cleanup still runs before an outer handler, and a
cleanup failure replaces the body's outcome.

`examples/example_files/mirage_exceptions` restores scoped mutable state in
Soma and checks identity, rethrow, cleanup replacement and cancellation.
`test-suite/misc/soma_exceptions.sh` runs the actual emitted backend cases
against real Lwt and checks native signatures. `SOMA_TEST_HVF=1` also boots
the complete example, native exception fixtures and an exit-bypass check.
These are tested shared runtime primitives; their native implementation is
part of the trusted runtime, not a formal proof of Lwt or native exceptions.

`cancel t` requests cancellation of a pending forked task and returns whether
it was pending; its awaiters receive `TaskFailed "cancelled"`. Cancelling an
awaiter, including the losing side of a race, does not cancel the shared task.
`await_within` leaves the underlying task running when its timer wins.
`new_context_key : io (context_key A)`, `get_context key`, and
`with_context key (Some value) body` provide a dynamically scoped value:
forked tasks inherit it, independent tasks cannot overwrite each other's
scopes, and waits, failures and cancellation preserve/restore those scopes.
`None` clears a value for the scope; outside a scope the value is `None`.
`free_context_key` releases the key; subsequent reads/scopes fail. Keep a key
alive until all tasks using it have ended. These are suitable for a guest
process's address-space context, without putting process policy in OCaml.
`test-suite/misc/soma_async_control.sh` checks extraction; set
`SOMA_TEST_HVF=1` to build and boot its assertions on an HVF-capable Mac.

`new_deferred (fun _ => body) : io (deferred A)` creates a computation without
running `body`. `force_deferred d : io A` starts it on first use and caches the
promise immediately, so concurrent forces share the pending computation as
well as its eventual result. Failure and cancellation remain cached; forcing
never retries the producer. A synchronous first-invocation exception is cached
too. Reentering a first force before the producer has returned its promise
fails. Task-local context comes from the first force, not creation. Cancelling
a force can cancel the shared promise and therefore affect its other waiters;
use a forked task and `await` when the computation needs protection from a
waiter's cancellation. An uncancellable underlying promise stays uncancellable.

Deferred handles belong to the values holding them, with no numbered runtime
table or explicit release operation. Once forced, the producer closure is
released; the result remains reachable through the handle. `Deferred n` cannot
manufacture a handle and matching a handle cannot reveal an ID. Native
`.definition` signatures can name `deferred A`, preserving the result type.
The current backend represents it as `'a Lwt.t Lazy.t` in `Soma_handles`.
The language API does not require application-specific OCaml glue; this
backend still generates OCaml and uses Lwt. It is not a C/native backend or a
proof of that runtime's semantics.

`examples/example_files/mirage_deferred` exercises sharing, failure, reentry,
context, cancellation and handle safety without any project foreign code.
`test-suite/misc/soma_deferred.sh`, with host `ocamlfind`/`lwt`, checks the
actual generated runtime branches, exception and result identity, and garbage
collection. Set `SOMA_TEST_HVF=1` to also execute the complete Soma program in
a Solo5 guest.

`new_reference value : io (reference A)` allocates a mutable location whose
lifetime follows its owners. `read_reference r`, `write_reference r value`
and `modify_reference r f` operate on that location. The last operation
computes, stores and returns the replacement without yielding; if computing
it raises an exception, no replacement is stored. Aliases see each other's
writes. References can form cyclic graphs, and unreachable cycles are
collectible. There is no global ID table or explicit free operation. Existing
`cell` handles retain their explicit `free_cell` semantics.

The current backend uses `'a ref`, named `'a Soma_handles.reference` in
`.definition` signatures. A typed native function sees the same location, not
a copy. Constructing `Reference n`, inspecting its number, or casting to an
incompatible value type fails. Native functions remain trusted to obey their
declared signatures and effect ordering. These primitives let a Soma program
own mutable state directly rather than require project-specific OCaml ref
allocation/read/write interpreters. Their runtime is tested, not formally
verified.

`examples/example_files/mirage_references` checks aliases, cooperative
updates, failure preservation, deferred reads, cycles and handle safety.
`test-suite/misc/soma_references.sh` checks native signatures and the actual
generated runtime, including physical identity and collection of unreachable
locations, payloads and cycles. `SOMA_TEST_HVF=1` adds the complete program's
Solo5 boot.

Buffers, signals and promises are for a program that does what a C or
OCaml one would: a page, a sector or a frame changed in place rather than
a string made of each, tasks that wait for one another rather than
polling a cell, OCaml's own promises awaited. A buffer, a signal and a
promise are OCaml values in the image (`Bytes.t`, a count and an
`Lwt_condition`, an `Lwt.t`), not numbers it looks up; a cell or a task
is, so `free_cell` and `forget` let one go. A buffer changes, so a native
function given one is called with `call`, in order with the other
actions. `examples/example_files/mirage_buffers/mirage_buffers.soma`
checks each buffer action, reads a disk's sectors into a buffer and
writes them back from it, wakes a waiting task with a signal and times
out another wait, and fails to read a freed cell and await a forgotten
task; `examples/example_projects/native_handles` has C fill a buffer
(`pattern.c`) and OCaml sum it and give promises (`later.ml`), one of
which fails. `dev/mirage-check.sh` boots both, and
`test-suite/misc/soma_buffers.sh` checks them without an image.

`examples/example_files/mirage_events/mirage_events.soma` is a server
that answers UDP pings and greets TCP connections, and, given its address,
a client whose one loop of `select` sees a timer of `after`, the UDP pong,
and the greeting and end of a `watch`ed connection, with `--soma-quiet`;
`dev/mirage-check.sh` boots both.

`examples/example_files/mirage_raw_clock/mirage_raw_clock.soma` writes
part of a line with `write`, and checks `random_bytes`, `monotonic_ns`
across a 10 ms sleep and `wall_clock`; `dev/mirage-check.sh` boots it, and
`test-suite/misc/soma_raw_actions.sh` checks its extraction, refuses a
nanosecond reading used as a `nat`, and runs the runtime's conversions on
fixed inputs.

The contracts check types, not runtime behavior; image testing still needs
`SOMA_MIRAGE_SWITCH` set to a switch with Mirage and solo5 installed.

`theories/Soma/Sandbox.v` (not in the prelude) makes a program a
MirageOS unikernel for Apple Silicon. Its `main : io unit` says what the
unikernel does, as data; building an `io` does nothing, the image runs it.

| Action | Type | What the image does |
| --- | --- | --- |
| `ret a` | `io A` | nothing; the result is `a` |
| `a ;; b`, `x <- a ;; b` | | `a`, then `b` (`bind`, in `io_scope`) |
| `print s` | `io unit` | a console line |
| `sleep n` | `io unit` | waits `n` seconds (`Mirage_sleep`) |
| `monotonic_ms` | `io N` | monotonic milliseconds since an arbitrary origin (`Mirage_mtime`), unaffected by wall-clock adjustments |
| `sleep_ms n` | `io unit` | waits `n : N` milliseconds (`Mirage_sleep`); large durations are split to avoid nanosecond overflow |
| `forever body` | `io A` | `body` again and again |
| `iterate step start` | `io A` | `step start`, then `step` of its result, and so on: a loop that carries a state (`step : S -> io S`) |
| `now` | `io (nat * nat * nat)` | the UTC time of day, `(hour, minute, second)` |
| `random n` | `io nat` | a random number below `n` (`Mirage_crypto_rng`) |
| `random_bytes n` | `io string` | `n` random bytes, from the same generator |
| `write s` | `io unit` | `s` on the console as it is, flushed: no line break added (`print` adds one) |
| `monotonic_ns` | `io int` | monotonic nanoseconds since an arbitrary origin (`Mirage_mtime`), as Rocq's primitive 63-bit integer (`PrimInt63.int`, OCaml's `int` in the image): cheap to read in a loop |
| `wall_clock` | `io (int * int)` | the UTC wall clock (`Mirage_ptime`): seconds since 1970-01-01 and the nanoseconds past them, as primitive integers |
| `spawn body` | `io unit` | runs `body : io unit` alongside the rest and returns at once. Actions take turns: one runs until it waits (for time, a connection, an event), then another does. A failure in `body` is reported (a `failure` event `during` `task`) and the image goes on; its `exit` stops the image, which keeps running until its tasks have ended |
| `fork body` | `io (task A)` | runs `body : io A` alongside the rest, as `spawn` does, and returns at once with a handle to its result |
| `await t` | `io (awaited A)` | waits for the task to end: `Completed a`, its result, or `TaskFailed why` (its body failed, or `t` is no task `fork` gave). Any task can await it, any number of times, each getting the same answer |
| `await_within t ms` | `io (option (awaited A))` | `await`, waiting `ms : N` milliseconds at most: `None` when the task is still running then (it goes on) |
| `new_cell a` | `io (cell A)` | a cell holding `a`, shared by whatever has it: handlers, spawned tasks, the main loop |
| `read_cell c`, `write_cell c a` | `io A`, `io unit` | what the cell holds; the cell holds `a` from now on |
| `modify_cell c f` | `io A` | the cell holds `f` of what it held, returned: in one step, which no other task's comes between |
| `call f` | `io A` | `f tt`, called in order with the other actions: for a function of a C or OCaml module that does something (`call (fun _ => buffer_get b 3)`) |
| `args` | `io (list string)` | the `--arg=...` given to the image, in order |
| `exit n` | `io A` | stops with exit code `n` |
| `serve port handler` | `io unit` | answers TCP connections on `port`: the first data a connection sends goes to `handler : string -> io string`, whose result is sent back before the connection is closed. Returns at once; the image keeps serving after `main` ends. |
| `fetch address port request` | `io fetched` | connects to the address (an IP address, or a host name, looked up as `resolve` does), sends `request`, returns what comes back before the other side closes (`Reply body`), or why there is nothing: `Refused` (nothing listens there), `TimedOut` (nothing answered within 10 seconds), `BadAddress` (neither an IP address nor a name that resolves: an `unresolved` event says why) |
| `resolve host` | `io resolved` | the IPv4 address of the host name, asked of the DNS resolvers the network gives the image (`Resolved address`), or why there is none (`Unresolved why`): not a host name, no such name, no IPv4 address, or no answer within 10 seconds |
| `https verb host port path headers body` | `io answered` | an HTTPS request (HTTP/1.1 over TLS): the name resolved, the server's certificate checked against the NSS certificate authorities for that name, the answer read to its end: `Answer status headers body` (header names in lower case, a chunked body joined), or why there is none (`Unanswered why`: no address, no connection, a certificate not trusted, no HTTP answer), within 30 seconds and up to 16 MB. `Host`, `Connection` and `Content-Length` are set by the request; a header with a line break is refused. `https_get host path` and `https_post host path content_type body` are the usual ones, on port 443; `header name headers` finds a header. |
| `listen port handler` | `io unit` | accepts TCP connections on `port`, each given to `handler : connection -> io unit`, which talks over it as long as it likes; the connection is closed when the handler ends. Returns at once; the image keeps listening after `main` ends. |
| `connect address port` | `io connected` | opens a connection to the address (an IP address, or a host name, as `fetch`) that stays open (`Connected c`), or says why there is none: `ConnectRefused`, `ConnectTimedOut` (10 seconds), `ConnectBadAddress` (with an `unresolved` event). `connect_within address port ms` gives up after `ms : N` milliseconds, looking the name up included |
| `send_checked c data` | `io tcp_write` | `TcpSent`, `TcpClosed` for an already closed link, or `TcpWriteError reason` for a failed write (which closes the link) |
| `send c data` | `io sent` | writes `data` as it is (`send_line c line` adds `"\n"`): `Sent`, or `SendClosed` when the connection is closed |
| `receive_line c` | `io received` | the next line, without its `"\n"` (or `"\r\n"`): `Line l`, or `Closed` when the connection ends first (a line left unfinished is dropped) |
| `receive_frame c seconds` | `io framed` | the next length-prefixed frame (four bytes of length, most significant first, then the bytes; `send_frame c data` sends one): `Frame data`, `FrameClosed` when the connection ends first, `FrameTimedOut` when no whole frame came within `seconds` (`0`: no limit; what arrived is kept for the next receive), or `FrameTooLarge` for a length over `max_frame` (1 MiB), which closes the connection |
| `receive_frame_up_to c seconds limit` | `io framed` | the same read, with an explicit per-read byte limit (0 through 4294967295); zero accepts empty frames only. Invalid limits fail before reading; oversized frames close the connection. For Kykeon's workspace protocol use `67108864` (64 MiB). The same extracted `Soma.Wire.take_frame` decoder enforces either limit |
| `receive_checked c ms` | `io tcp_read` | raw bytes as `TcpData data`, orderly EOF as `TcpEof`, timeout as `TcpTimedOut`, or transport failure as `TcpReadError reason`. The timeout and buffering rules are the same as `receive`; an error closes the link |
| `receive c ms` | `io chunk` | what the connection has received, as TCP delivered it, cut nowhere: what was left past the last line or frame taken, or else the next bytes to arrive, waiting `ms : N` milliseconds at most (`0`: no limit): `Chunk data` (never empty), `ChunkClosed` when the connection ends first (it is closed), or `ChunkTimedOut`. For connections accepted or opened; lines, frames and `receive` read the same bytes, in order |
| `watch c` | `io unit` | the connection's bytes as `Linked` events of `select` (and `mailbox`): `LinkBytes` as they arrive, then `LinkClosed`; for a connection the program opened, as `listen_mailbox` does for those it accepts. Again does nothing |
| `after ms tag` | `io unit` | a `Timer tag` event for `select` once `ms : N` milliseconds have passed; returns at once |
| `select ms` | `io (list event)` | what came in since the last `select`, oldest first: `Linked e` (a `link_event` of `listen_mailbox`'s or `watch`ed connections), `Datagram port host source_port data` (UDP), `Timer tag`. When nothing has, it waits, `ms : N` milliseconds at most (`0`: not at all), and is `nil` when the time is up: a select over everything, for a program with one loop. `mailbox` takes only the `Linked` events and leaves the rest to `select` |
| `udp_listen port` | `io unit` | the UDP datagrams to `port` as `Datagram` events of `select`; returns at once, and the image keeps receiving after `main` ends |
| `udp_send address port source_port data` | `io bool` | one UDP datagram to the IP address and port, from `source_port` (`0`: one the stack picks): `true` when it went out, `false` for an address that is not an IP address or a datagram the stack could not send |
| `disk_info name` | `io (option (nat * nat))` | the sector size in bytes and the number of sectors of the block device `name` (`--block:name=FILE`); `None` when it is not attached |
| `disk_read name sector count` | `io (option string)` | `count` sectors from `sector` on, as bytes; `None` past the end or on a failed read |
| `disk_write name sector data` | `io bool` | `data`, whole sectors of it, written from `sector` on: `false` for a read-only disk, data that is not whole sectors or goes past the end, or a failed write |
| `new_buffer n` | `io buffer` | a buffer of `n` bytes, each `0`: OCaml's `bytes`, read and written in place, freed by the collector once nothing has it |
| `buffer_size b` | `io nat` | its length |
| `buffer_get b i`, `buffer_set b i v` | `io (option nat)`, `io bool` | the byte at `i`; `v`'s low 8 bits written there. Past the end: `None`, `false`, nothing written (so for every buffer action) |
| `buffer_read b i n`, `buffer_write b i s` | `io (option string)`, `io bool` | `n` bytes from `i`, as a string; the string's bytes from `i` on |
| `buffer_copy src i dst j n`, `buffer_fill b i n v` | `io bool` | `n` bytes of `src` from `i` to `dst` from `j` (the same buffer included, as through a copy); `n` bytes from `i`, each `v` |
| `buffer_get_uint b i w`, `buffer_set_uint b i w v` | `io (option nat)`, `io bool` | a little-endian number of `w` bytes (1, 2 or 4; another width is `None`, `false`), as AArch64's and x86's memory has them |
| `buffer_get_word b i`, `buffer_set_word b i w` | `io (option word64)`, `io bool` | 8 bytes, little-endian, as a `Soma.Word64` word |
| `disk_read_into name sector count b i` | `io bool` | `disk_read`, into the buffer from `i`, with no string between: `false` where `disk_read` is `None`, or when the sectors do not fit in the buffer |
| `disk_write_from name sector b i n` | `io bool` | `disk_write` of the buffer's `n` bytes from `i` |
| `send_buffer c b i n` | `io sent` | `send` of the buffer's `n` bytes from `i`; bytes past its end fail the task |
| `new_signal` | `io signal` | a signal tasks wait on, counting from 0 |
| `notify s` | `io unit` | counts one more, and wakes every task waiting for it |
| `signal_count s` | `io nat` | how many times it was notified |
| `wait_signal s seen ms` | `io (option nat)` | waits until the count is past `seen`: `Some` the count, at once if it already is, or `None` when `ms : N` milliseconds pass first (`0`: as long as it takes). A task reads the count, looks at what it waits for, then waits for a count past what it read, so a `notify` in between is not missed |
| `free_cell c` | `io unit` | the cell is gone: what it held can be freed, and reading or writing it fails the task |
| `forget t` | `io unit` | the image forgets the task's result (the task goes on if it is running): it can be freed, and `await t` is `TaskFailed` |
| `await_promise p` | `io A` | waits for what an OCaml module promised (`promise A`, its `'a Lwt.t`): its value, or the task fails as the promise did |
| `local_address` | `io (option string)` | the image's own IPv4 address, as the network configured it; a program that uses it gets a network stack |
| `close c` | `io unit` | closes the connection; again does nothing |
| `connect_within address port ms` | `io connected` | `connect`, giving up after `ms : N` milliseconds (`ConnectTimedOut`) rather than 10 seconds: for a program that dials from its loop |
| `listen_mailbox port` | `io unit` | accepts TCP connections on `port` into the mailbox: each one's opening, the bytes it receives and its end are `mailbox`'s. The program may `send` on one and `close` it (which posts no end). Returns at once; the image keeps listening after `main` ends. |
| `mailbox ms` | `io (list link_event)` | what `listen_mailbox`'s connections did since the last `mailbox`, oldest first: `LinkOpened c host` (accepted, from that IP address), `LinkBytes c data` (bytes as TCP delivered them), `LinkClosed c` (the other side ended it). When nothing has, it waits for something, `ms : N` milliseconds at most, and is `nil` when the time is up: a select over the connections, for a program with one loop |

The links (`listen`, `connect`, `send`, `receive_line`, `receive_frame`,
`close`) keep one connection per peer open, and carry lines or frames,
a frame holding any bytes, line breaks included. A connection is a number
the image knows it by (`Connection id`); after `Closed` or `FrameClosed`,
a program reconnects with `connect`. So a program can tell a peer that
never answered (`ConnectRefused`, `ConnectTimedOut`), one that went quiet
(`FrameTimedOut`) and one that hung up (`Closed`, `FrameClosed`, `SendClosed`).

The image keeps, for each connection, what it has received past the last
line or frame it returned, so a receive returns exactly one message
however TCP cut the bytes; lines and frames are taken from the same
bytes, in order. A receive that times out leaves the read it started for
the next receive, so nothing is read twice or lost. Taking the first
message of what was received is pure and in `Soma.Wire`
(`theories/Soma/Wire.v`, which Sandbox exports): `take_line`,
`take_frame`, `split_lines`, `split_frames` and `receive_chunks` (chunks
fed one after another), with `Example`s on fixed chunks (a message split
across chunks, several in one chunk, a partial one kept, an empty line, a
length prefix that arrives alone) and theorems that what is kept never
holds a whole message (`split_lines_kept`, `split_frames_kept`), and that
the messages and what is kept do not depend on how the bytes were cut
into chunks: they are those of all the bytes at once
(`receive_lines_chunking`, `receive_frames_chunking`). The
image's `Soma_rt.take_line` and `Soma_rt.take_frame` call these extracted
definitions through generated adapters; there is no separate native decoder
algorithm to keep in agreement. `frame_roundtrip` proves that encoding a
payload and decoding it recovers both the payload and arbitrary following
bytes, provided the length fits its 32-bit prefix and the receiver's limit.
`frame_roundtrip_default` specializes this to the 1 MiB limit.

`Soma.Wire` is not only the image's: a program built for the machine
imports it (`Require Import Soma.Wire.`) without becoming a unikernel, so
it frames and splits what it sends and receives with the functions an
image uses. Where strings are OCaml's and `nat` is its `int` (an image,
and a program built for the machine), `take_frame` reads a
length and takes a frame by offset (`String.get`, `String.substring`),
one copy of its bytes, instead of taking the string apart a character
at a time, which copies the rest at each one; `split_at_walk` and
`take_frame_walk` are those functions a character at a time, and
`split_at_walk_eq` and `take_frame_eq` say they're the same, so the
theorems above hold of what runs. Pantheon's node service frames its
requests and answers with them (its `node_net.soma`), as its unikernel
does through Sandbox's `send_frame` and `receive_frame`.

`examples/example_files/mirage_link_server` and `mirage_link_client`
exchange lines on one connection (`dev/mirage-check.sh`'s `link-*` cases),
and `test-suite/misc/soma_links.sh` checks them through `--no-image`.
`mirage_frame_server` and `mirage_frame_client` exchange frames, an
empty one and one of two lines among them (`frame-*` cases), and
`test-suite/misc/soma_frames.sh` checks them through `--no-image`, with
programs that misuse a receive's or a connect's result.

`http_response body`, `http_get path`, `http_path request` and `crlf` build
and read HTTP. `++` appends strings wherever a `string` is expected (see
`Strings.v`).

```rocq
Require Import Sandbox.

main : io unit :=
  print "serving HTTP on port 8080" ;;
  serve 8080 (fun request =>
    ret (http_response ("You asked for " ++ http_path request))).
```

`soma build prog.soma` (or `rocq c prog.soma`) checks the program and,
since it requires `Sandbox`, builds `prog.hvt` next to `prog.vo`
(`toplevel/somaMirage.ml`, called from `toplevel/ccompile.ml`). Only a
program is built so, a `.soma` file; a Rocq `.v` file that requires
`Sandbox` is a library:

1. `main` must exist and have type `io unit`.
2. `main` is extracted to `prog.ml` (strings as `char list`, with Stdlib's
   `ExtrOcamlString`) into a MirageOS project with a generated `config.ml`,
   `soma_rt.ml`, which runs an `io` with Lwt, and `unikernel.ml`.
   `gradual.ml` is the extracted gradual runtime, or a stand-in when the
   program has no casts. A `raise` or `unk` that the image reaches is
   reported and the image exits with 1; in a `serve` handler, it ends that
   connection only.
3. A program that uses `serve`, `fetch`, `listen` or `connect` gets a network stack
   (`generic_stackv4v6`, DHCP); the image runs under `solo5-vmnet`, which
   gives it an address on the Mac's vmnet network (macOS 26 or later, no
   root). The others have no network device. One that uses `resolve`,
   `https`, `fetch`, `connect` or `connect_within` (which take host names)
   is a web image (`net-web/`): MirageOS's `dns_client` device on
   the stack (`generic_dns_client`, with `generic_happy_eyeballs`), and the
   packages `tls-mirage`, `ca-certs-nss`, `x509` and `domain-name`.
   dns-client links TLS itself (for DNS over TLS), so a web image is about
   13 MB to a network image's 7, `https` or not; a program that only
   serves or listens has no DNS. The
   HTTP/1.1 of `https` (the request, and reading the answer) is in
   `soma_rt.ml`, with no library; DNS and TLS are in `unikernel.ml`.
4. The project is built for solo5's `hvt` target in the opam switch
   `$SOMA_MIRAGE_SWITCH` (for example `hvf`: a switch with the hvf-mac
   repository of solo5-mac, with `mirage`, `opam-monorepo`, `solo5-hvt` and
   `solo5-vmnet`), and `rocq c` says how to run the image; `soma run`
   runs it.

The projects are kept in `$SOMA_MIRAGE_DIR`, or else
`~/.cache/soma/mirage` (`plain/` and `net/`), so `mirage configure`
and fetching the dependencies only happen the first time for each, about
15 s; later builds take about a second. The dependencies are locked with
`opam monorepo lock` given the switch's own repositories (their copies
under opam's root, so the versions match its installed dune and compiler,
with dune-universe's opam-overlays before the default repository) and
opam's global variables, then fetched with `make pull`. That is the lock
`make depends` would write, without needing a default opam switch:
opam-monorepo asks opam for the current switch and ignores `OPAMSWITCH`.
`make depends`' other step, installing the switch's packages, isn't run;
they are the MirageOS tools the switch must already have. A project
whose dependencies were never fetched (a Makefile, no `duniverse`) is set
up again. Each one's `build.log` has its last build's output.
`SOMA_MIRAGE_BUILD=0` skips the image.

The image runs in `$SOMA_MIRAGE_MEM` MB of memory, or `soma.toml`'s
`[image] memory`, 256 by default, which the command to run it states (`solo5-hvt --mem=256 -- prog.hvt`). Memory
is small and bursty for a server: each closed connection leaves state that
TCP keeps for some seconds (about 6 KB; 2500 fast connections hold 15 MB
for under 20 s), and strings, lists of characters, make garbage. So the
runtime collects more eagerly (`space_overhead` 40) and compacts the heap
once a burst of requests is over; with these, the HTTP server example
answers 15000 requests in 64 MB, where it ran out after about 5500
before, at about 4500 requests per second one at a time and 12000 ten at
a time. An image given `--soma-stats` prints what it holds every 2
seconds:

```
soma-stats: requests=2500 open=0 memory=56648KB live=19120KB free=36503KB ocaml_heap=14577KB major_collections=10
```

(`memory`, `live` and `free` are the unikernel's whole heap, network
buffers included; `ocaml_heap` is OCaml's part of it.)

### What a run comes to

The runtime says what happens to the image as events, one JSON object a
line after `soma-event ` on its console, for whoever runs it to read:

| Event | Fields |
| --- | --- |
| `start` | `memory_kb`, `network` |
| `serving` | `port` |
| `listening` | `port` (of `listen`, `listen_mailbox` with `mailbox`, or `udp_listen` with `udp`) |
| `failure` | `during` (`main`, or `request` or `task`: the image goes on), `kind` (`cast`, with `expected` and `actual`; `raise`; `unknown`; `stack_overflow`; `out_of_memory`; `exception`, with `message`) |
| `memory_pressure` | `live_kb`, `memory_kb`: live memory passed 80% |
| `alive` | `requests`, `live_kb`, every 10 seconds |
| `unresolved` | `address`, `why`: an address `fetch` or `connect` was given that is neither an IP address nor a name that resolves |
| `exit` | `code`, `reason` (`finished`, `program`: its `exit n`, `failure`) |

An image given `--soma-quiet` prints no events: for a program whose
console is a stream of its own, such as a terminal's bytes through
`write`. Its exit code still says how it ended, and run-time errors are
still printed.

`main` is computed by the runtime (it is extracted as a function), so that
a failure while building it is an event like any other, and so are the
stack overflows and out-of-memory exceptions that Lwt does not catch. The
allocator giving up has no event: the image aborts at once.

`soma run` reads the events rather than showing them, and says at the end
what the run came to: that the program exited with a code, stopped on a
run-time error (and which), ran out of stack or memory (with its memory
and the last live memory reported), was stopped, or stopped without saying
why (with its last line); and how many requests failed, with the last
failure. `soma run --events` shows the events, and ends with the outcome
as JSON:

```
soma-outcome {"outcome":"failed","kind":"cast","message":"expected a string, but got a nat","expected":"a string","actual":"a nat"}
```

`dev/mirage-check.sh` checks these diagnoses (`exits`, `cast_failure`,
`stack_overflow`, `out_of_memory`).

### Supervision

`theories/Soma/Orchestrate.v` (not in the prelude) has what a run comes
to as types: an `outcome` (`Finished`, `Exited code`, `Failed f`,
`Stopped`), a `failure` (`CastFailure expected actual`, `Raised`,
`Unknown`, `StackOverflow`, `OutOfMemory memory_mb live_mb`, `Crashed
reason`), and a `decision` (`Done`, `Restart`, `RestartWith memory_mb`). A
`policy` decides from the outcome, the image's memory and how many times
it was restarted. `default_policy limit ceiling` never runs again what
would fail again (`deterministic`: a failed cast, `raise`, `unk`, a stack
overflow), what ended well or was stopped; doubles the memory after
running out, up to `ceiling` MB; and stops after `limit` restarts. Its
library proves all three (`default_never_reruns_deterministic`,
`default_stops_after_limit`, `default_within_ceiling`).

`soma run --supervise FILE` runs the image, and when the run ends asks the
program's `restart_policy` (or `default_policy 3 1024`) what to do: the
outcome is given to it as a term of Soma and the decision evaluated by
Soma, so that what runs is the policy that is proved. A run stopped from
outside ends supervision. `examples/example_files/mirage_supervised/mirage_supervised.soma`
is a server with its own policy, whose `.exp` proves that it never runs
again a failed cast, stops after 5 restarts and asks for at most 512 MB;
`dev/mirage-check.sh` checks a run out of memory in 64 MB, run again with
128 (`supervised`).

```sh
soma run examples/example_files/mirage_http_server/mirage_http_server.soma              # prints its IP
soma run examples/example_files/mirage_fetch/mirage_fetch.soma -- --arg=<that IP>
```

`dev/mirage-check.sh` builds the examples (`examples/example_files/mirage_*/`), boots
each image and checks its console and exit code, the network cases with one
unikernel serving and another fetching from it, and one fetching a page over
HTTPS from the internet and refusing a self-signed certificate
(`mirage_https`).

```sh
soma run examples/example_files/mirage_https/mirage_https.soma                       # mirageos.org
soma run examples/example_files/mirage_https/mirage_https.soma -- --arg=mempool.space
```
`dev/mirage-check.sh --no-image` stops after the check above and does not boot.

Soma's installed libraries can be required by their short name, as
Corelib's are (`sysinit/coqloadpath.ml`), so `Require Import Sandbox.` finds
`Soma.Sandbox`.

Not yet: IPv6 addresses from `resolve` (and so for names given to `fetch`
and `connect`), names for `udp_send`, TLS for `listen` and `serve` (an
HTTPS server), and client certificates.

## JSX: components and apps

`theories/Soma/JSX.v` (not in the prelude) brings ReasonReact's JSX
to Soma, for components and apps that are checked, and can be proved
about, but not yet compiled to JavaScript.

```rocq
Require Import JSX.

Greeting {name : string} := <p> "Hello, " name "!" </p>.
page := <main> <Greeting name="world" /> <> <i> "a" </i> <b> "b" </b> </> </main>.
render page.   (* "<main><p>Hello, world!</p><i>a</i><b>b</b></main>" *)
```

- `<tag attr=value ...> children </tag>` and `<tag ... />`, for a tag in
  lowercase, are an HTML element, `node tag attributes children`. Its
  attributes are strings, except `onClick=action` and the other `on...`,
  events, whose value is an action: an element is an `element A`, `A` the
  type of its actions.
- `<Component prop=value ...> children </Component>` is
  `Component (prop := value) ... (children := [...])`: a component's props
  are implicit arguments, `Greeting {name : string} := ...`, so a missing or
  unknown prop is an error when the program is checked. A prop of type
  `Any` takes any value, checked when the element is evaluated.
- `<> children </>` is a fragment.
- An attribute value or a child is an atom or a term in braces,
  `{to_string count}`; a string child is a text element (a coercion).
- `render` turns an element into HTML, leaving events out. An element
  that HTML writes without an end tag (`void_tags`: `br`, `hr`, `img`,
  `input`, `meta`, ...) has none when it has no children: `<br />` is
  `<br>`.

JSX is read by the lexer under `Set JSX Syntax`, which `JSX.v` exports
(`parsing/cLexer.ml`, `parsing/g_constr.mlg`). With it, `<` directly
followed by a letter opens a tag and `</` directly followed by a letter
closes one, so a comparison is written `x < y` (`x<10` and `<=` are
unaffected); `<>` and `</>` are a fragment, so "not equal" is `!=`. These
are keywords that source text cannot produce otherwise (they end with a
zero-width space), and other files are read as before.

An app (`app S A`, made with `make_app init update view`) has a state of
type `S`, starts at `init`, changes with `update : A -> S -> S` on each
action, and shows it with `view : S -> element A`, whose events produce
actions. `state_after app actions` is the state after a list of actions,
what a theorem about the app's behavior is about.
`examples/example_files/reason_counter/reason_counter.soma` proves that a counter stays within its
limit whatever buttons are clicked, with no type annotation outside the
theorems.

GCIC made an implicit argument `?` whenever its binder occurs nowhere in the
rest of the function's type. This is now only for type arguments
(`map {A B} (f : Any)`): an implicit value, like a prop, a type class
instance or a Program proof, is inferred or an error, as in Rocq.

## Limitations and known gaps

- **No mechanized proofs.** Graduality and conservativity come from the
  design (typing untouched, rules follow the paper). They are not proven
  for this implementation.
- **Germ-free casts.** The paper factors injections through *germs* (`? -> ?`,
  `I ? … ?`). This fork injects the original head type directly. In GCIC^G
  this should be observationally equivalent, and it avoids universe
  arithmetic in the kernel.
- **Sorts are consistent only when cumulative.** Without `?`, consistency
  is conversion, or cumulativity where Rocq allows it (the result and
  codomains), so `nat : Prop` and moving a type to a lower universe are
  static errors. Casts between sorts compare levels in the universe graph.
  The extracted runtime only compares Prop, Set and Type, since levels are
  erased. Everything cast lives below the single global universe
  `Corelib.Gradual.Gradual.gradual`. A large type such as `list Type`, or
  a universe-polymorphic record, can still be cast. When a cast would
  need a type above `gradual`, elaboration says so instead of reporting
  a plain type mismatch, e.g. for `Set : Any`:
  `Cannot cast from "Type" to "Any": "Type@{Set+1}" lives above the universe
  of gradual types (Corelib.Gradual.Gradual.gradual), so no cast was inserted.`
- **SProp** is not supported, because the axioms quantify over `Type`.
- **Indexed families** go beyond the paper, which only treats parameters.
  The behaviour is a first-order index check. The indices a rebuilt
  constructor computes are compared with the target ones: `?` is
  compatible with anything, and distinct constructors are a mismatch
  (`raise`). Anything undecided, such as a neutral index, leaves the cast
  stuck (`test-suite/success/gradual_vec.v`).
- **VM / native compilation** treat the axioms as opaque. Under
  `Gradual Typing`, `vm_compute`, `native_compute` and `Compute` fall back
  to `cbv`.
- **Reducts of `match` on `?` may live above `gradual`** when the match
  returns a large type. This is harmless for computation, but such a
  reduct would not re-typecheck.
- **Bidirectionality is checking, not synthesis.** With an expected
  type, argument inference is delayed until that type has been unified
  with the result, so `cons 1 (cons true nil) : list Any` checks both
  elements at `Any`. Leading type arguments are still inferred first, so
  an explicit one wins over the expected type: `@cons Any 1 nil : list nat`
  is a cast from `list Any`. At type `Any` itself, type parameters that
  nothing determines are set to `Any`, so `cons 1 (cons true nil) : Any`
  is a `list Any` cast to `Any`; explicit ones still win
  (`@cons nat 1 nil : Any` is a `list nat`).

## Versions

The kernel version is Rocq 9.3.0. `tools/configure/configure.ml` sets
`major = 9`, `minor = 3`, and `patch = Release 0`. Rocq's standard
library is vendored separately, at tag V9.2.0, commit
`8dd155bc10529814202f8f4c643e5ae6c2c88fa6` (`theories/Stdlib/README.md`).
This tree does not record a build or a test run of that kernel together
with that Stdlib. The suite result below is commit `d011c4b1cf`
(26 Oct 2026), which has no `theories/Stdlib`. The vendor commit is
`93b778c3bc` (27 Oct 2026).

`make test-suite` and `make -C test-suite` do not run every check:

- Lean. `test-suite/misc/soma_lean.sh` is part of the suite. It exits 0
  without checking a proof when `elan` is missing (`no elan: skipped`)
  or lists no toolchain (`no Lean toolchain: skipped`).
- OCaml builds. `test-suite/misc/soma_ocaml.sh` sets `SOMA_OCAML_BUILD=0`
  and does not build or run the OCaml program. `dev/ocaml-check.sh` does
  that outside the suite: a small executable, `async_tasks`, `soma
  extract` of that program, and `bonsai_counter`. It needs Soma built,
  opam, Node 22 or later, and Chrome.
- Mirage images. The suite does not boot a unikernel. `dev/mirage-check.sh`
  builds and boots the `examples/example_files/mirage_*` images,
  `counter_server`, and `wasm_add`'s image, and checks `soma run`'s
  diagnosis of a run. It needs Soma built and the Mirage switch
  (`$SOMA_MIRAGE_SWITCH`, for example `hvf`) with the Apple Silicon
  solo5 tools. The network cases run under `solo5-vmnet` (macOS 26 or
  later). `dev/mirage-check.sh --no-image` only type-checks those programs.
  `test-suite/misc/soma_no_image*.sh` does the same with no Mirage switch.

## Tests

For a Soma project in Git, `soma test` discovers `.soma` entry points
recursively under `test/` and `tests/`, builds them and checks their paired
`.exp` expectations. Give paths to use another layout:

```sh
soma test                         # first non-empty diff in the waterfall below
soma test --full                  # every entry point; establish dependency records
soma test --changedSince HEAD     # staged, unstaged and untracked changes
soma test --changedSince main     # branch changes plus working-tree changes
soma test --changedSince main --listTests
soma test checks/ crypto/smoke.soma --no-image
```

Without an explicit mode, select the first non-empty project diff:

1. Unstaged changes, including untracked files.
2. Staged changes.
3. `HEAD` against the current branch's remote-tracking branch.
4. `HEAD` against the default branch.

Only that diff is used; the lower steps are not combined with it, even when
the chosen diff affects no tests. Tests execute against the current working
tree, including its staged and unstaged edits. All steps are scoped to the
Soma project, so changes elsewhere in a containing Git repository do not
hide a later relevant diff.

The remote branch is the configured remote-tracking upstream, or the
same-named branch on the selected remote when no upstream is available.
The selected remote is the branch's configured remote, otherwise `origin`,
otherwise the only remote. The default branch is that remote's symbolic
`HEAD`; without it, use an existing local `init.defaultBranch`, or a unique
local `main`/`master`. Comparisons use locally available refs and never fetch.
Detached HEAD skips the current-branch comparison. If no comparison is
available, run the full suite conservatively; if comparisons are available
but all empty, select only tests with missing or uncertain records.

`--changedSince REF` overrides this waterfall and includes all differences
between that commit and the working tree, plus untracked files. Its
comparison is against the given commit, rather than its merge base;
pass a merge-base commit explicitly when that is the intended comparison.
`--full` runs every discovered entry point regardless of differences or
dependency records. It cannot be combined with `--changedSince`.
`--listTests` prints one selected project-relative path per line and does
not build or write cache records. Other runners can consume those paths;
external scripts and image boot tests remain their responsibility. Use
`--no-image` to check without building Mirage images.

Successful test builds record the files the compiler actually loaded,
including indirect imports, expectation imports and folder rules. No
second parser guesses imports from source text. An edit to an unrelated
existing Soma module can skip its tests; edits to imported modules or
their expectations select the dependent entry points. Records also
include source hashes. With an explicit `--changedSince`, changing the Git
baseline cannot hide source changes since the last successful test build.
Automatic selection instead focuses on the chosen diff; it does not union
changes from lower-priority steps through those source snapshots.

The first run, missing or invalid records, changed toolchains/environments,
added or removed sources, changed configuration, extensions or other
resources widen selection. Tests with external project dependencies keep
running until their dependency graph can be recorded completely. Records
live under `.soma-cache/.tests/`; deleting the cache is safe. A failed
test removes its record and stops the run with that test's exit status.
Git-ignored source dependencies cannot certify a skipped test. Discovery
does not follow symbolic links. This command checks project Soma tests;
the inherited compiler and shell test suite described below still uses
its existing runner.

The last recorded full run of the inherited Rocq test suite
(`make -C test-suite`) is commit `d011c4b1cf` (26 Oct 2026, "Gradual
Typing: recursion through Dyn, without a guard"): 2751 tests passed and
3 failed, on macOS. That record is for that commit. HEAD has moved
since, and the run predates the vendored Stdlib. It was the
conservativity check for that tree: none of its files import `Gradual`,
apart from the gradual tests below. The three failures were
environmental and also failed on the unmodified base:
`coq-makefile/latex1` (LaTeX), `coq-makefile/timing-per-file` (GNU
`time` output), and `misc/bench-render` (removed since, with
`rocq-devtools`). The unit tests need `ounit2`. The checks outside
that run are under Versions.

- `test-suite/success/gradual.v`: reduction rules in every machine, Ω, flag toggling
- `test-suite/success/gradual_vec.v`: indexed families (`vec`, `Fin`, `eq`): index checks, stuck casts on neutral indices, `match` on `?`
- `test-suite/output/Gradual.v`: the elaborated terms (cast insertion)
- `test-suite/misc/gradual_extraction.sh`: one program checked three ways. Each case's value holds as a syntactic normal form under `lazy`, `cbv`, `cbn`, `simpl` and `vm_compute`, and the extracted OCaml agrees with it, except for the documented differences, which are marked in `main.out`
- `test-suite/coqchk/gradual_register.v`, `test-suite/misc/gradual_rocqchk.sh`: `rocqchk` installs the rules of gradual primitives registered in the module it checks, and validates `Corelib.Gradual.Gradual` itself

### Persistent files in Sandbox

`read_file name : io (option string)` reads a named file; `None` means
missing and `Some ""` means an existing empty file. `write_file name data`
replaces bytes and `append_file name data` appends in order, creating a
missing name. Names are opaque keys, matching `Sandbox.Files`, with no host
path interpretation. Device errors stop the image; they never become a
missing-file result. Operations share a lock, so read/append/write handlers
cannot interleave an append's read and write.

A program using these operations gets a dedicated Solo5 block device named
`storage`. Make a zeroed disk once, then reuse it across boots:

```sh
truncate -s 8M storage.img
solo5-hvt --block:storage=storage.img -- mirage_storage.hvt
solo5-hvt --block:storage=storage.img -- mirage_storage.hvt
```

`soma run mirage_storage.soma` does the same with `storage.img` in the
current directory: it creates the zeroed 8 MiB disk the first time and keeps
it, so running it again in the same directory prints the next boot
(`soma_storage_run_disk.sh` checks this with stand-ins for opam and solo5).

The example prints `boot 1`, then `boot 2`; `dev/mirage-check.sh --storage-only`
builds it and checks those boots. `--no-image` type-checks the same generated
backend and interfaces without requiring Mirage or Solo5. The misc test
`soma_aa_storage_runtime.sh` also executes an extracted Soma program against
the generated backend using a sector-file adapter, then reopens the disk in
another process. It tests overwrite, ordered append, missing/empty files,
independent names and binary values, a failed commit, and capacity failure.

The device is dedicated to this format, not a filesystem or a host directory.
Two alternating snapshots have bounded, checksummed payloads; the new header
is written after its payload, leaving the previous committed bank intact.
Each bank uses at most 16 MiB; the usable data is the smaller of half the disk
and 16 MiB, less the header and name/length metadata. Updates rewrite a full
snapshot. Capacity exhaustion and read-only/write failures stop the operation
without updating the in-memory file map. Recovery accepts a valid previous
snapshot when the other bank is invalid; it refuses a disk with no valid
snapshot and nonzero headers. Checksums detect corruption, not malicious edits.
Durability follows the block driver's successful-write contract; this is not
a proof about host power loss, disk caches, or adversarial storage.

`theories/Soma/StorageSpec.v` formalizes an ordered-sector commit protocol
for initialized stores. Every accepted event prefix recovers the old or
complete new snapshot, and an acknowledged commit recovers the new one.
The model enforces payload-before-header and header-before-acknowledgment
ordering, and connects complete snapshots to the `Sandbox.Files` read/write
laws. Native decoding/checksum validation and device persistence still need
to establish the model's premises. `soma_storage_snapshot_recovery.sh`
checks the generated backend across multiple generations, empty and
multi-sector payloads, each interrupted write and torn prefixes at header
field boundaries, including a full sector persisted before an error.

The generated backend uses the sector interface documented by
[mirage-block](https://github.com/mirage/mirage-block/blob/main/src/mirage_block.mli).

The first snapshot writes its complete header, then rewrites that header with
an acknowledgement marker in padding byte 56 before reporting success. This
keeps a damaged acknowledged first header from looking like an interrupted
first-header prefix and reopening as empty. If the marker rewrite fails, the
in-memory map stays unchanged; reopening may recover the complete snapshot.
Older valid headers with zero padding remain readable, but cannot gain this
protection retroactively. `soma_aa0_storage_first_receipt.sh` covers checksum
damage and every sector-prefix interruption of the marker rewrite.

`Native.Promise_bind_borrowed owner body next` preserves a direct native
provider/bind call's consumed-owner argument frame. The owner is not inspected
or retained by the continuation. Native liveness can release a dead owner
before the provider; bytecode retains its argument slot until the tailcall to
`Lwt.bind`. The provider, bind semantics, exceptions, cancellation and dynamic
context are otherwise those of `Native.Promise_bind`.

`Native.tail_invoke primitive` fuses a final `Invoke primitive Return` into a
native tailcall. It returns the provider's exact value or promise, preserves
synchronous exceptions, and drops the extra invocation frame before entering
the provider. Use it when the original native control flow tailcalls a final
primitive rather than invoking it before further dispatch.

`Native.word_length text` gives a byte length in `PrimInt63.int` for existing
pure machine-word policies. Its logical definition takes the low 63 bits of
`String.length`; extraction uses OCaml's `String.length` directly. Native
strings fit in that range, with no traversal, wrapper, or added assumption.

`OCaml Native External Type buffer := "Buffer.t".` and
`OCaml Native External Callback create : PrimInt63.int -> buffer := "Buffer.create".`
name existing OCaml types and values by absolute paths. Ordinary native
`Type`/`Callback` declarations remain relative to their companion module.
External declarations need no handwritten forwarding module: generated typed
bindings call the named native module directly. Native path, signature and
labels participate in declaration identity and the native ABI manifest;
the OCaml compiler checks that the actual external type/value matches.

`OCaml Native Tag directory : kind -> bool := "Vfs.Dir" 1.` tests an existing
named constructor. `OCaml Native Case builtin : kind -> option string :=
"Vfs.Builtin" 1.` borrows its payload when matched. The explicit arity is
checked by OCaml patterns; zero-argument cases return `option unit`, and
multiargument cases return right-nested products in argument order. Tags
can ignore inline-record payloads. Inputs may be declared native types or
Soma's built-in `exception_value`; the latter permits typed filtering of caught
native exceptions without a handwritten conversion adapter. Use qualified
constructor paths for built-in exceptions;
constructor paths, arities and signatures are hashed. Generated typed matches
use no casts or runtime layout offsets, and incorrect ABI declarations fail
OCaml compilation. Unqualified constructor names use the input type's module.

`Native.vector_size` observes a native array's readonly header as a natural;
`Native.vector_word_size` gives its low 63 bits for machine-word policies.
The vector model records that immutable size alongside its opaque identity.
Extraction uses `Array.length` directly, preserving ordinary native caller
expressions and allocation behavior. Mutable element operations stay native
effects; extracted code still cannot construct or inspect opaque vectors.
`Native.quadruple` represents a native flat four-tuple with borrowed components,
complementing `Native.triple` for typed native interfaces.

`OCaml Native Immutable Record file := { label:string; lines:Native.vector string }.`
creates a structural logical record and a single shared native record module.
Constructors, projections and pattern matches remain ordinary pure Soma;
typed native extraction maps them to the shared record ABI. Mutable fields
are rejected. This preserves native caller expression shapes for readonly
field observations, while mutable element storage remains explicit effects.

`OCaml Native External Value args : Native.vector string := "Sys.argv".`
declares a checked `Native.callback unit (Native.vector string)` getter.
Calling it returns the named native value directly, with no copying or extra
application. This also exposes existing reference cells and native function
values, whose reads and later calls remain separate explicit Soma operations.

External values and callbacks can also name qualified symbolic operators, for
example `"Stdlib.(=)"` or `"Stdlib.(+.)"`. The generated binding still checks
the declared OCaml type. Type and record field references use identifier paths.
A polymorphic external value declares named type parameters before its value
signature. Supply those parameters to the checked getter and then call it with
unit to obtain the native value at that instance.

An external value can apply the named function to one checked OCaml string
literal. For example:

```coq
OCaml Native External Value padded : nat -> string :=
  "Printf.sprintf" With "%02d".
```

The generated getter applies the literal when called and returns the resulting
native function. The OCaml compiler checks the format and result signature.
Literal characters are escaped as string data in the generated binding.

`OCaml Native External Exception division_by_zero := "Stdlib.Division_by_zero".`
declares a checked `Native.callback unit exception_value` getter for a
nullary external OCaml exception constructor. The path uses uppercase module
and constructor names. OCaml checks that the constructor expression has type
`exn`. Calling the getter returns the original exception value; use
`Native.Throw` or `Native.Promise_fail` to choose where it is raised.

`Native.loop_values step finish initial` runs an unbounded native loop over
ordinary state functions. It calls `finish` before each step, and stops as soon
as the observer returns a result in `Some`. On `None`, it calls `step` once and
continues with that state. Use it when the state functions already expose all
operations and the loop should avoid allocating an effect thunk or progress
tag on every transition. Its logical definition describes an ordinary
`Native.Loop` program.

`Native.List_map mapper items` uses the native `List.map` with an opaque
native callback, preserving element order, native tail-modulo-cons behavior,
exception identity, callback scope and consumed-input ownership. It introduces
no traversal bound or logical effect evaluator.

`Native.Promise_map_borrowed owner body next` preserves the direct native
provider/map call's consumed-owner frame, matching `Promise_bind_borrowed`.
Native liveness can release dead owners before the provider, while bytecode
keeps its incoming argument slot until the map. Exceptions, cancellation and
saved context follow the actual `Lwt.map` boundary.

`Native.New_callback3`, `New_callback4` and `New_callback5` complement the
two- and six-argument constructors with one native curried closure.
`Native.Call_callback2` through `Call_callback6` apply a callback at its
full arity in a single native call frame; unary `Call_callback` remains
available for explicit partial application. Bodies execute only on saturation,
with no intermediate program evaluation or fresh closure between arguments.

`Native.Pure_callback` and `Native.Pure_callback2` expose an ordinary pure
Soma function as an opaque native callback handle. They preserve the supplied
native function itself, including its curried arity, rather than creating an
entry program on every invocation. Native calls remain explicit effects;
there is no callback evaluator in the logic. This avoids per-element bridge
allocations when a native array/list traversal calls pure Soma policy.

`OCaml Native Assertion Factory unreachable : unit -> unit -> A := 123 8.`
declares a checked native factory for a closed assertion callback. Reading the
native descriptor prepares the factory; applying that factory to `tt` creates
a thunk, and applying the thunk raises `Assert_failure`. The payload retains
the supplied positive line and nonnegative column and the native compilation
unit's `__FILE__`. A project can embed the authenticated output in the original
unit to retain its filename and constant pool. The two function arguments must
be positional, nondependent `unit` values; the answer must have a native
representation. Leading type parameters are allowed.

Keeping creation separate from invocation preserves the native compiler's
closed-function sharing and bytecode's fresh closures at the original creation
phase. No exception is raised or allocated while preparing the factory or its
thunk. A failed invocation raises a fresh synchronous exception with the same
allocation as the original closed assertion. Location data participates in
native metadata identity; there is no arbitrary OCaml expression or logical
effect evaluator. `test-suite/misc/soma_native_assertion_factory.sh` compares
actual compiler output against original assertions in native and bytecode.

`OCaml Native Assertion Function Factory invalid : unit -> input -> answer :=
42 28.` prepares a closed `fun _ -> assert false` callback for an ignored native
argument. The factory trigger is positional `unit`; the ignored input is also
positional and may have any native representation. Neither value may affect
the result type. Leading type parameters are supported. Preparing the factory
or creating a callback does not allocate or raise its exception. Invocation
raises the original fresh synchronous assertion at the fixed in-unit location,
without retaining or inspecting the input. The original unit-only assertion
command and its existing generated products are unchanged. The function form
has a separate appended native metadata tag and includes its coordinates and
signature in semantic/native ABI identity. See
`test-suite/misc/soma_native_assertion_function_factory.sh` for typed arguments,
closed sharing, ignored callbacks, 64MiB input, ownership, exact allocations
and location invalidation in native and bytecode.

`OCaml Native External Thunk Factory failure : unit -> unit -> A :=
"Stdlib.invalid_arg" With "negative index".` prepares a factory for the closed
callback `fun () -> invalid_arg "negative index"`. Reading the descriptor and
creating a callback do not invoke the target. Only the final thunk call applies
the existing native function to its static string argument. The target remains
a validated native value path; the literal is escaped data. The two positional
`unit` arguments and native answer type are checked, including leading type
parameters. Generated universal annotations reject less general native targets.
In-unit embedding retains original literal pooling, synchronous exceptions,
promise identity and invocation-time native context.

`OCaml Native Construct Factory number : unit -> word -> token := "N".`
prepares a factory for a closed callback that constructs tag `N` with its input.
The result must be a declared native polymorphic variant, the tag must exist, and the
payload must match its checked type (`unit` for a nullary tag). Parametric
variants and function-valued payloads retain their logical types and borrowed
native values. The first argument creates the callback at its original phase;
the next applies the constructor. Both factory forms retain native closed-code
sharing and bytecode's fresh callback closures, with no per-invocation program
or tuple bridge. Their target/literal/tag/schema data participates in native
provenance. `test-suite/misc/soma_native_closed_factories.sh` checks both modes,
original allocation/identity/ownership behavior and semantic-hash invalidation.

`OCaml Native Get Deferred read : owner -> unit -> string :=
"cell" "Target.text".` prepares an ordinary owner-to-thunk function. Creating
the thunk borrows only its owner; invoking it reads the current field chain.
The first unqualified field uses the receiver's native record namespace;
subsequent fields may specify their native record modules. Paths contain only
validated identifiers. The receiver must be a declared native record/type and
the trigger is positional `unit`; generated typed bindings check every native
field and the final result, including callback and promise results. A compiler
barrier preserves the one-owner closure instead of merging its curried arity.
No logical native evaluator or runtime program bridge is introduced.

`OCaml Native External Defaulted Function lookup : string -> string -> result :=
"Target.lookup" Using lookup_call.` prepares a closed positional adapter for a
named function and a closed declared native callable schema. Its signature
must match all required schema arguments and the result. Required labels are
supplied by the generated adapter; optional parameters are omitted so the
native function retains its defaults. The named implementation is also checked
against the complete callable schema. Creation does not invoke the function;
partial calls keep native default timing. Closed native sharing and bytecode
creation phases match direct callbacks without a captured receiver or argument
tuple. Native symbol, labels/default schema and deferred field paths contribute
to semantic and native ABI identities. See
`test-suite/misc/soma_native_deferred_fields.sh` and
`test-suite/misc/soma_native_defaulted_function.sh` for both-backend allocation,
identity, live-state, failure, promise/context/cancellation and Weak checks.

`OCaml Native External Bound Function head : context -> list string -> result :=
"Target.head_tail" Binding "tail" false Using head_tail_call.` prepares a
closed positional function that fixes one required boolean label. The checked
callable must contain that required `bool` label exactly once; optional labels
keep the native function's defaults. The remaining required arguments and
result must exactly match the declared positional function. The entire named
implementation is checked against its native callable schema, including the
bound label. Creation and partial application do not call the target or its
defaults. The generated closure contains no captured callable/invoker and no
per-call program or argument tuple. Native closed sharing and bytecode closure
creation match a direct `fun context args -> Target.head_tail ~tail:false
context args`. The symbol, full callable schema, bound label and boolean all
contribute to semantic and native ABI identities. See
`test-suite/misc/soma_native_bound_boolean_function.sh` for native/bytecode
sharing, allocations, default/partial/failure timing, borrowed values/promises,
context/cancellation, Weak lifetimes, native type rejection and invalidation.

Immutable record projections use named generated schema getters. Pure field
reads retain their expression order and allocate no temporary projection
closures per access, including bytecode execution.

`Native.Borrowed_scope owner before next` preserves a direct synchronous
caller's incoming argument frame through `before`, then releases the frame
before tail-entering `next`. The owner is not artificially pinned: native
liveness may release it sooner while bytecode retains its incoming slot.
Body and continuation exceptions retain their ordinary synchronous scopes.

`Native.call_then callback argument next` is defined as `Bind` after
`Call_callback`, with a fused native boundary. It avoids an intermediate
callback program and nested program tuples while preserving direct callback
argument/continuation frames, exceptions and context. It adds no evaluator or
logical assumption.

Native polymorphic variants may carry type parameters:

```rocq
OCaml Native Polymorphic Variant event (A : Type) := ["Value":A; "Closed"].
OCaml Native View inspect : forall (A:Type), event A -> Native.result A unit.
OCaml Native Construct value : forall (A:Type), A -> event A := "Value".
```

Multiple parameters use `(A:Type; B:Type)`. Parameters have sort `Type` or
`Set`; schemas retain them in their logical opaque family, so `event string`
and `event bool` remain distinct types. Payloads may refer to parameters,
including inside functions, promises, products and other native schemas.
`View` and `Construct` check the instantiated logical payload types and emit
ordinary typed native matches/constructions; no casts or layout offsets are
needed in their generated bindings. A descriptor can quantify over type
parameters or select a concrete instance. Native callback descriptors also
accept leading type parameters, for example a generic external identity.
Generated universal annotations reject native implementations that are less
general than the descriptor they implement.

Each generated schema has one shared parameterized OCaml type. Its source,
parameter list, tag order, payload types and generated product participate in
native provenance. The logical family adds no evaluator or axiom; extracted
consumers cannot inspect its opaque placeholder representation. The native
and bytecode ABI, logical type separation, borrowed payload/callback lifetimes,
and an actual Solo5 consumer are checked by
`dev/native-parametric-variant-check.sh`.

Native callable schemas may begin with named `Type` or `Set` parameters,
for example `OCaml Native Callable mapper:=forall(A B:Type),forall(label:string),A->B.`
The leading parameters define an opaque native type family, preserving their
logical order and identity. Remaining named binders describe OCaml labels.
`OCaml Native Apply` accepts either universally quantified or concrete
instances and checks its argument/result types against the instantiated logical
signature. Generated schema modules, typed universal bindings, ABI manifests
and Source hashes retain these parameters and labels. Values are borrowed
unchanged; this declaration does not add a native evaluator.
When a result parameter is instantiated with a function type, `Apply` consumes
only the value binders of the original schema and returns that function
unchanged. It preserves the callable's original partial-application boundary,
including the timing of target effects and deferred effects in returned functions.
`dev/native-callable-compatibility-check.py` retains independent cold-cache
baseline/candidate projects, schema and program products, manifests, logical
hash reports and a SHA256 receipt in the requested output directory.

### Closed full-application native field and literal functions

`OCaml Native External Value run : owner -> arg -> answer := "Target.run"
Reading "cell" "Target.payload" AtFullApplication.` prepares a closed native
function equivalent to `fun owner arg -> Target.run owner.cell.Target.payload arg`.
The signature has one or more positional arguments; its first argument is a
declared native record type. The field path is nonempty and consists only of
native identifiers. Leading type parameters and native type families are
supported. The actual native compiler checks every field and the target's
argument/result types, including opaque external records. Field lookup and
all target calls wait until full application. A partial function retains the
owner and rereads its current field chain when called; it does not capture an
earlier field value. This form can preserve an original closed function's
identity and sharing without allocating a wrapper around a prepared getter.

`OCaml Native External Value run : first -> last -> answer := "Target.run"
With "/" After 1 AtFullApplication.` prepares the closed native function
`fun first last -> Target.run first "/" last`. `After` ranges from zero to the
number of positional function arguments, inclusive. The literal can therefore
appear at the beginning, middle or end. Partial application does not call the
target. The existing `With literal AtFullApplication` syntax and its metadata
representation are unchanged.

Both forms use checked native metadata rather than an OCaml expression escape
or a logical effect evaluator. They preserve borrowed native inputs/results,
synchronous exceptions and native promises, and introduce no extra per-call
tuple/effect bridge. Their two metadata variants are appended after existing
variants, preserving existing cache tags. Target paths, field paths, owner
types, literal contents, insertion positions and arity participate in semantic
and native ABI identity. `test-suite/misc/soma_native_full_field_literal.sh`
compares real generated output with original functions in native and bytecode,
including unary/parametric fields, live mutation after partial application,
closed sharing, exact allocation, exceptions, promise/context/cancellation,
Weak ownership, native rejection of invalid fields/results, and independent
field/literal/position hash invalidation.

### Static native function composition

`OCaml Native Static Compose run : public_call := outer With inner.` combines
existing typed native getters into a closed function. `inner` supplies the
first argument of `outer`; all inner arguments precede the remaining outer
arguments. For example, an inner `owner -> effects` and outer
`effects -> word -> string -> answer` produce `owner -> word -> string ->
answer`. The result may instead be a declared native callable, retaining its
required or optional labels. Target/inner labels are independent of the public
labels and are supplied according to their own checked signatures.

`OCaml Native Static Prefix run : public_call := target With config.` binds
an existing native value getter to the first target argument. The prefix must
be a direct native value or native float literal, so binding cannot move a
creation-time native call into an invocation. Its object is borrowed; mutable
contents remain live. Both commands check the complete argument/result types,
including leading type parameters. A native descriptor with type parameters
uses the corresponding leading parameters of the new descriptor. A mismatched
signature or a callback whose creation may execute native code is rejected.

The allowed function inputs are closed external value functions, the checked
full-application literal/field functions, checked positional compositions and
other static functions. This is typed native metadata, with no arbitrary OCaml
expression, new axiom or logical effect evaluator. The backend emits the full
closed call directly and supplies native labels. It does not allocate an inner
wrapper at invocation or reintroduce a per-call program/tuple bridge. Inner and
outer calls wait for full application. Native/bytecode function sharing, native
argument/result identity, faults, promise/context/cancellation behavior and
partial-callback ownership retain the original closed wrapper semantics.
Nested metadata, labels and all referenced native operations participate in
semantic/native ABI identity; changing an inner literal invalidates the
composed descriptor and its consumers. The new metadata tag is appended,
leaving existing tags and products unchanged.

`test-suite/misc/soma_native_static_function.sh` checks actual generated native
and bytecode functions against original wrappers: labelled/optional targets
and public APIs, defaults, multi-argument/nested compositions, polymorphic
bytes and returned functions, exact creation/call allocations, mutable prefix
contents, full-call timing/faults, raw promises/cancellation, dynamic context,
Weak ownership and transitive hash invalidation.

`OCaml Native Static Compose Scope prepared : ((owner -> effects) *
public_call) := outer With inner.` prepares the inner function and its composed
function together. The first export has exactly the inner getter's function
type; the second has the checked composition signature, including public
labels. Both exports come from one scope. A literal-bearing inner function
has one literal site, and the composed callback refers to that same prepared
function. Its closure graph therefore retains the exported inner callback for
as long as the original composed callback does. An existing native function
value is borrowed directly as the first export, preserving its identity.

Use a composition scope when the inner callback is also public and its literal
identity or lifetime must be shared with the composed callback. Each inner
function body is emitted once, followed by its composition and the returned
pair, with no per-call getter or wrapper allocation. Native closure sharing,
bytecode closure creation, partial-application timing and caller ownership
follow the original pair of local function definitions. The scope has a
separate appended metadata tag. Its component metadata and complete signatures
participate in native ABI and semantic hashes. It introduces no evaluator or
axiom. `test-suite/misc/soma_native_static_scope.sh` compares real generated
code with original scopes in native and bytecode, covering literal identity,
closure sharing, borrowed existing functions, generic payloads, exact faults,
Weak retention/release of the inner callback and caller, and exact construction
and invocation allocations. Existing standalone static-function output remains
unchanged.

### Open native variant rows

An OCaml API that returns `[> ...]` exposes width polymorphism: a caller can
combine its values with additional tags. Preserve that API with a row parameter:

```soma
From Soma Require Import Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native Open Polymorphic Variant token (Row : Type) :=
  ["N" : PrimInt63.int; "V" : string; "O" : string].
OCaml Native Construct Factory number : forall Row : Type,
  unit -> PrimInt63.int -> token Row := "N".
Definition number_factory {Row : Type} :=
  Native.Export (Native.Call_callback (number Row) tt).
Definition main (Row : Type) := number_factory (Row := Row).
```

The generated native family has the form
`type 'row t = ([> ...] as 'row)`. Each exported polymorphic function can be
instantiated at a different wider row. `Construct` and `Construct Factory`
retain typed payloads and their existing callback creation phases. There is
exactly one row parameter, which cannot occur inside a payload; payloads may
include ordinary functions. `View` rejects open variants because an ordered
sum of the declared cases cannot represent additional caller tags.

The row family is opaque symbolic native metadata, without an axiom, logical
callback evaluator or arbitrary OCaml expression. The generated typed native
boundary rejects a primitive with the wrong result type. An appended metadata
case distinguishes open from closed row ABIs and invalidates their hashes;
existing closed and parameterized schemas keep their original output.

`test-suite/misc/soma_native_open_variant.sh` checks independent wider-row
instantiations, direct construction, borrowed string/function payloads,
native/bytecode constructor sharing, exact creation and dynamic-payload call
allocation, natural Weak collection, invalid schemas/views/ABIs and row-kind
hash changes. Closed factories, variant aliases, callable functions, static
functions/scopes and record aliases also pass. A separate cold-cache comparison
with the preceding compiler keeps 22 older products and the complete
contract/witness hash report byte-identical.

### Full-application static arguments

`OCaml Native Static Apply run : signature := target With [first; second]
AtFullApplication.` binds a nonempty prefix of typed native getter values.
It leaves at least one public argument. The generated wrapper creates those
values and calls the target only when all public arguments are supplied:

```soma
OCaml Native Open Polymorphic Variant token (Row : Type) :=
  ["N" : PrimInt63.int; "V" : string].
OCaml Native Construct Function number : forall Row : Type,
  PrimInt63.int -> token Row := "N".
OCaml Native Construct Function variable : forall Row : Type,
  string -> token Row := "V".
(* consume: configuration -> (word -> token Row) ->
   (string -> token Row) -> string -> list (token Row) *)
OCaml Native Static Apply tokenize : forall Row : Type,
  string -> list (token Row) := consume With [configuration; number; variable]
  AtFullApplication.
```

`Construct Function` prepares a closed one-argument constructor function;
nullary cases use a unit argument. When it is a static argument, its literal
function body is created inside the wrapper's full-call scope. Native closed
sharing and bytecode freshness follow the corresponding `fun payload ->
\`Tag payload` expression. Use an ordinary external value getter to borrow an
already public function; expanding its blueprint would create another function.

Every target and supplied value must be a declared closed native getter. The
checker compares complete instantiated argument/result types, retains generic
parameters, and checks public required/optional labels independently of the
target's labels. Literal and field function getters stay functions: their
bodies are not invoked while preparing a callback argument. Nested static
applications are supported. Function-valued literal getters are called at the
full application point. There is no per-call native program or argument tuple
bridge and no arbitrary expression, logical evaluator or additional axiom.

The metadata cases are appended, and all supplied blueprints, their order and
labels participate in the ABI and semantic hashes. Existing static compose,
prefix and scope emission remains unchanged. The native/bytecode suite
`test-suite/misc/soma_native_static_application.sh` checks quiet partials,
constructor/literal alias matrices, live fields and bound configuration,
labels/defaults, generic bytes/functions and wider variant rows, synchronous
faults, exact promises, Lwt context/cancellation, exact allocation and natural
Weak lifetimes, including consumed-owner collection inside the target tail
continuation, plus invalid signatures and literal hash invalidation.
