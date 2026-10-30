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

```coq
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
opam switch create ./ ocaml-base-compiler.4.14.2 --no-install
opam install --switch=. dune ocamlfind zarith
eval $(opam env --switch=. --set-switch)
make dunestrap
dune build soma-runtime.install soma-core.install
_build/install/default/bin/soma run my_file.soma
```

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
- `soma repl [FILE]` is an interactive session (`rocq repl`, prompt
  `Soma <`), with FILE's definitions loaded first (`-l FILE`).
- `soma build --fill FILE` writes the proofs that `The rest follows.`
  found in `FILE.proof` (see Proof sentences).
- `soma help` lists the commands, and `soma build --help` the options of
  build and run (those of `rocq c`).

A program `FILE.soma` has its lemmas and theorems in `FILE.proof`, next
to it: a `.soma` or `.lang` file cannot start a proof (`Theorem`, `Lemma`,
a `Definition` proved interactively, ...; `vernac/vernactypes.ml`), while
Rocq's `.v` files can. Checking `FILE.soma` (`rocq c`, so `soma build` and `soma
run`) reads the program, then `FILE.proof` in the program's environment
(`toplevel/ccompile.ml`): the proofs see what it defines and imports, JSX
included, without importing anything. A proof that does not hold fails the
build, with its location in `FILE.proof`, and no `.vo` or MirageOS image is
made; the theorems are part of the program's library. `soma build
FILE.proof` and `soma run FILE.proof` stand for `FILE.soma`.
`examples/example_files/reason_counter.proof` and `examples/example_files/reason_components.proof` are
examples; `test-suite/misc/soma_proof.sh` tests it.

### Proof sentences

A `.proof` file imports `theories/Soma/Proof.v` (and only a `.proof`
file does), so that a proof can be written as sentences that say what
each step does, for people and agents to read without replaying it.
Each sentence is checked: one that states the goal or a fact fails
unless it is the goal or holds, so the text cannot drift from the
proof.

```coq
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
| `We consider whether a < b as H.` (or `<=`, `=`) | for numbers, a case with `H : a < b` and one with its opposite; `a <? b` is then `true` or `false` |
| `We use induction on x.` | a case for each constructor of `x`, whose arguments and induction hypotheses each case takes and assumes |
| `We use strong induction on n.` | for a number: proves the goal for `n` assuming it for every smaller number, which is taken and assumed |
| `The rest follows.` | searches for the rest of the proof, and reports it as sentences (below) |

`The rest follows.` searches for the rest of a proof
(`plugins/soma_proof/soma_rest.ml`): it takes and assumes what the goal
gives, then tries `soma_auto`, computing, the hypotheses, the program's
and its projects' lemmas, unfolding their definitions at the top of the
goal (not Rocq's), and Rocq's lemmas that could prove the goal, for 20
seconds at most. It reports the proof it found as sentences, each printed
so that it reads back as what it states. `soma build` says how many proofs
were found, `soma build -v` prints them, and `soma build --fill` writes
each in place of its `The rest follows.` in `FILE.proof`, indented as the
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
a `.proof` file, a tactic acts on one goal at a time (`Default Goal
Selector "!"`): with several goals open, each is focused with a bullet or
braces. Notations in a sentence are read as in a theorem's statement:
`*` is on `nat`s unless scoped, as in `(sqrt 2 * sqrt 2 = 2)%R`. All the
example `.proof` files are written in sentences, `sqrt2_irrational.proof`
(top down, with `It suffices to show that ... as ...` blocks and strong
induction) and `reason_counter.proof` (cases and induction) among them;
the tactics they replace are in their history.

### Macros: `.lang` files

Macros are defined in `.lang` files, with `Macro name args := body.`: a
macro is a function from the code of its arguments (`args : list syntax`)
to the code it stands for (a `syntax`), in `theories/Soma/Macro.v`. A use
of a macro in scope, `name a b`, looks like a call: when it is
internalized (`interp/constrintern.ml`), the code of `a` and `b` is quoted
into `syntax` values, the macro is evaluated on them, and the `syntax` it
returns is read back as code and checked in place of `name a b`
(`vernac/somaMacro.ml`). A local variable of the same name hides the
macro. `syntax` has names, numbers, strings, applications, `fun`s and
holes; other code (a `match`, a notation like `a + b`) is `Opaque`, which a
macro can return but not look into. `MacroError "..."` fails the
expansion with that message, at the use; so does a run-time error in the
macro. Expansions nested 1000 deep stop with an error.

Macros are in scope only where they are asked for:

- `FILE.lang`, next to `FILE.soma`, is read before the program, so its
  macros are in scope in `FILE.soma` and `FILE.proof` (and in `soma repl
  FILE.soma`).
- Another `.lang` file is in scope where it is loaded, `Load
  "other.lang".`, or, compiled by itself (`rocq c other.lang`), where it
  is imported, `Require Import other.` (not with `Require` alone).
- `Macro` can only be used in a `.lang` file, and the `Macro` library
  (`syntax`, `App`, ...) is only in scope there: a `.lang` file is loaded in
  a module of its own that imports it.

`examples/example_files/macros.lang` and `examples/example_files/macros.soma` are an example;
`test-suite/misc/soma_macros.sh` tests it.

Soma source files end in `.soma`. `rocq c`, `Load`, `-l` and `rocq dep`
also accept Rocq's `.v` (Corelib and the Rocq libraries are `.v`), and
`.lang`; given a name without an extension, they look for `.soma` first,
then `.v`, then `.lang`.
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
- Stdlib's `ZArith`, `QArith`, `Reals`, `Qreals` and `Lra`: integers `Z`,
  rationals `Q`, reals `R` with `sqrt`, `Q2R` from rationals to reals, and
  the `lra` tactic. `QArith` opens `Q_scope`, which the prelude closes again,
  so `3` is still a `nat`; rationals are written `(1 # 2)%Q` and reals
  `(sqrt 2)%R`. Loading `Reals` takes hello world from 0.12 to 0.15 s.

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
README) and built and installed with the rest, so `From Stdlib Require ...`
works without flags.

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

```coq
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

### Run-time errors

A cast that fails reduces to `raise`, which keeps nothing but its type, and
`raise` only spreads to what looks inside it: `append "Hello, " raise` is
the string `"Hello, "` ending in `raise`. A term evaluated (`Compute`,
`Eval`, a bare term) whose value has a `raise` in it is printed as far as
it was computed, followed by what went wrong:

```coq
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
prints it as `Run-time error: ...` and exits.

## Architecture

The kernel stays the CIC kernel. The cast calculus (CastCIC) is encoded with
three **axioms** that the kernel knows about through its *retroknowledge*,
the same mechanism used for primitive integers:

```coq
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

So that proofs stay proofs, saving a proof (`Qed`, `Defined`) warns
(`gradual-proof`) when it relies on the primitives in a way its
statement does not account for. That covers a proof that is `unk` or
`raise`, and a proof that uses `cast`, `unknown` or `err` when its
statement does not. Lemmas about gradual programs, such as
`succ_dyn 41 = 42`, and proofs without gradual primitives stay silent:

```
Lemma by_cast : 0 = 1. Proof. exact (cast (0 = 0) (0 = 1) eq_refl). Qed.
(* Warning: by_cast: the proof uses gradual primitives its statement does not
   (cast), so it may not hold in Rocq (see Print Assumptions). *)
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

```coq
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

Extraction erases types, which casts need. So OCaml extraction compiles
each `cast A B t` to a call to a small runtime, `Gradual_rt`
(`plugins/extraction/gradual_rt.ml`), with runtime descriptions of `A`
and `B`. The runtime applies the rules above. The extracted file embeds the
runtime: it only needs the OCaml standard library, so it also builds for
MirageOS unikernels.

```coq
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

  ```coq
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

`theories/Soma/Sandbox.v` (not in the prelude) makes a program a
MirageOS unikernel for Apple Silicon. Its `main : io unit` says what the
unikernel does, as data; building an `io` does nothing, the image runs it.

| Action | Type | What the image does |
| --- | --- | --- |
| `ret a` | `io A` | nothing; the result is `a` |
| `a ;; b`, `x <- a ;; b` | | `a`, then `b` (`bind`, in `io_scope`) |
| `print s` | `io unit` | a console line |
| `sleep n` | `io unit` | waits `n` seconds (`Mirage_sleep`) |
| `forever body` | `io A` | `body` again and again |
| `now` | `io (nat * nat * nat)` | the UTC time of day, `(hour, minute, second)` |
| `random n` | `io nat` | a random number below `n` (`Mirage_crypto_rng`) |
| `args` | `io (list string)` | the `--arg=...` given to the image, in order |
| `exit n` | `io A` | stops with exit code `n` |
| `serve port handler` | `io unit` | answers TCP connections on `port`: the first data a connection sends goes to `handler : string -> io string`, whose result is sent back before the connection is closed. Returns at once; the image keeps serving after `main` ends. |
| `fetch address port request` | `io (option string)` | connects to the IP address, sends `request`, returns what comes back before the other side closes; `None` if the connection fails or nothing answers within 10 seconds |

`http_response body`, `http_get path`, `http_path request` and `crlf` build
and read HTTP. `++` appends strings wherever a `string` is expected (see
`Strings.v`).

```coq
Require Import Sandbox.

main : io unit :=
  print "serving HTTP on port 8080" ;;
  serve 8080 (fun request =>
    ret (http_response ("You asked for " ++ http_path request))).
```

`soma build prog.soma` (or `rocq c prog.soma`) checks the program and,
since it requires `Sandbox`, builds `prog.hvt` next to `prog.vo`
(`toplevel/somaMirage.ml`, called from `toplevel/ccompile.ml`):

1. `main` must exist and have type `io unit`.
2. `main` is extracted to `prog.ml` (strings as `char list`, with Stdlib's
   `ExtrOcamlString`) into a MirageOS project with a generated `config.ml`,
   `soma_rt.ml`, which runs an `io` with Lwt, and `unikernel.ml`.
   `gradual.ml` is the extracted gradual runtime, or a stand-in when the
   program has no casts. A `raise` or `unk` that the image reaches is
   reported and the image exits with 1; in a `serve` handler, it ends that
   connection only.
3. A program that uses `serve` or `fetch` gets a network stack
   (`generic_stackv4v6`, DHCP); the image runs under `solo5-vmnet`, which
   gives it an address on the Mac's vmnet network (macOS 26 or later, no
   root). The others have no network device.
4. The project is built for solo5's `hvt` target in the opam switch
   `$SOMA_MIRAGE_SWITCH` (`hvf` by default: a switch with the hvf-mac
   repository of solo5-mac, with `mirage`, `opam-monorepo`, `solo5-hvt` and
   `solo5-vmnet`), and `rocq c` says how to run the image; `soma run`
   runs it.

The projects are kept in `$SOMA_MIRAGE_DIR`, or else
`~/.cache/soma/mirage` (`plain/` and `net/`), so `mirage configure`
and fetching the dependencies (`make depends`, which needs the network) only
happen the first time for each, about 15 s; later builds take about a
second. Each one's `build.log` has its last build's output.
`SOMA_MIRAGE_BUILD=0` skips the image.

```sh
soma run examples/example_files/mirage_http_server.soma              # prints its IP
soma run examples/example_files/mirage_fetch.soma -- --arg=<that IP>
```

`dev/mirage-check.sh` builds the examples (`examples/example_files/mirage_*.soma`), boots
each image and checks its console and exit code, the network cases with one
unikernel serving and another fetching from it.

Soma's installed libraries can be required by their short name, as
Corelib's are (`sysinit/coqloadpath.ml`), so `Require Import Sandbox.` finds
`Soma.Sandbox`.

Not yet: DNS names (`fetch` takes an IP address), TLS, UDP, block devices
and key-value stores, and state shared between `serve` handlers.

## JSX: components and apps

`theories/Soma/JSX.v` (not in the prelude) brings ReasonReact's JSX
to Soma, for components and apps that are checked, and can be proved
about, but not yet compiled to JavaScript.

```coq
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
- `render` turns an element into HTML, leaving events out.

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
`examples/example_files/reason_counter.soma` proves that a counter stays within its
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

## Tests

The whole Rocq test suite (`make -C test-suite`) passes with these changes.
That is the conservativity check: none of its files import `Gradual`, apart
from the gradual tests below. The last full run was at `d011c4b1cf`:
2751 tests passed and 3 failed, on macOS. All three failures are
environmental and also fail on the unmodified base:
`coq-makefile/latex1` (LaTeX), `coq-makefile/timing-per-file` (GNU
`time` output) and `misc/bench-render` (since removed, with
`rocq-devtools`). The unit tests need `ounit2`.

- `test-suite/success/gradual.v`: reduction rules in every machine, Ω, flag toggling
- `test-suite/success/gradual_vec.v`: indexed families (`vec`, `Fin`, `eq`): index checks, stuck casts on neutral indices, `match` on `?`
- `test-suite/output/Gradual.v`: the elaborated terms (cast insertion)
- `test-suite/misc/gradual_extraction.sh`: one program checked three ways. Each case's value holds as a syntactic normal form under `lazy`, `cbv`, `cbn`, `simpl` and `vm_compute`, and the extracted OCaml agrees with it, except for the documented differences, which are marked in `main.out`
- `test-suite/coqchk/gradual_register.v`, `test-suite/misc/gradual_rocqchk.sh`: `rocqchk` installs the rules of gradual primitives registered in the module it checks, and validates `Corelib.Gradual.Gradual` itself
