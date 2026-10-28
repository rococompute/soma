# Lightlang: GCIC^G, the variant that gives up normalization

Lightlang's kernel is this fork of the Rocq Prover (based on 9.3.0). It adds
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
dune build rocq-runtime.install coq-core.install rocq-core.install
_build/install/default/bin/light run my_file.light
```

`light` is Lightlang's command line (`topbin/light.ml`):

- `light build FILE` checks and builds a program as `rocq c FILE` does, with
  the same options, then deletes the files `rocq c` made (`.vo`, `.glob`,
  `.aux`), printing `Deleted FILE.vo` for each, and prints the names of the
  files it keeps: the `.hvt` image of a Mirage program. `light build -v FILE`
  first prints the values of the program's bare terms. (`rocq c` keeps the
  `.vo`, for files that `Require` the program.)
- `light run FILE [-- ARGUMENTS]` checks the program in a temporary
  directory, so that it leaves no files, and prints the value of its last
  bare term; a program that requires Mirage is built into an image, which
  is run with ARGUMENTS (under `solo5-vmnet` when it uses the network).
- `light help` lists the commands.

Lightlang source files end in `.light`. `rocq c`, `Load`, `-l` and `rocq dep`
also accept Rocq's `.v` (Corelib and the Rocq libraries are `.v`); given a
name without an extension, they look for `.light` first, then `.v`.
`rocq makefile`, `rocq doc` and editor modes still only know `.v`.

Every file starts with the Lightlang prelude, `theories/Lightlang/Lightlang.v`,
loaded right after Rocq's Prelude. It exports, from `theories/Lightlang`:

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

Pass `-no-lightlang-prelude` for plain Rocq, where each part of the
Lightlang prelude can be imported on its own (`From Lightlang Require Import
Strings Lists Show.`), or `-no-prelude` to load no prelude at all, Rocq's
included (`-noinit` and `-no-lightlang-prelude`). The
Lightlang prelude is skipped under `-boot` and `-noinit`, so Corelib, Ltac2,
Stdlib and the prelude itself are built as plain CIC. The inherited Rocq
test-suite runs with `-no-lightlang-prelude`, and the gradual tests import
`Gradual` explicitly.

Rocq's standard library is vendored in `theories/Stdlib` (V9.2.0, see its
README) and built and installed with the rest, so `From Stdlib Require ...`
works without flags.

The unknown type `Any` (`unknown Type`) was called `Dyn` until the commit that
renamed it; `GROK_*.md`, `gradual-coverage.md` and
`dev/gradual-lattice/results/` predate that and still say `Dyn`.

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
Compute succ_dyn true.   (* = raise : nat, a runtime type error *)

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

## Mirage: programs as unikernels

`theories/Lightlang/Mirage.v` (not in the prelude) makes a program a
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
Require Import Mirage.

main : io unit :=
  print "serving HTTP on port 8080" ;;
  serve 8080 (fun request =>
    ret (http_response ("You asked for " ++ http_path request))).
```

`light build prog.light` (or `rocq c prog.light`) checks the program and,
since it requires `Mirage`, builds `prog.hvt` next to `prog.vo`
(`toplevel/lightlangMirage.ml`, called from `toplevel/ccompile.ml`):

1. `main` must exist and have type `io unit`.
2. `main` is extracted to `prog.ml` (strings as `char list`, with Stdlib's
   `ExtrOcamlString`) into a MirageOS project with a generated `config.ml`,
   `lightlang_rt.ml`, which runs an `io` with Lwt, and `unikernel.ml`.
   `gradual.ml` is the extracted gradual runtime, or a stand-in when the
   program has no casts. A `raise` or `unk` that the image reaches is
   reported and the image exits with 1; in a `serve` handler, it ends that
   connection only.
3. A program that uses `serve` or `fetch` gets a network stack
   (`generic_stackv4v6`, DHCP); the image runs under `solo5-vmnet`, which
   gives it an address on the Mac's vmnet network (macOS 26 or later, no
   root). The others have no network device.
4. The project is built for solo5's `hvt` target in the opam switch
   `$LIGHTLANG_MIRAGE_SWITCH` (`hvf` by default: a switch with the hvf-mac
   repository of solo5-mac, with `mirage`, `opam-monorepo`, `solo5-hvt` and
   `solo5-vmnet`), and `rocq c` says how to run the image; `light run`
   runs it.

The projects are kept in `$LIGHTLANG_MIRAGE_DIR`, or else
`~/.cache/lightlang/mirage` (`plain/` and `net/`), so `mirage configure`
and fetching the dependencies (`make depends`, which needs the network) only
happen the first time for each, about 15 s; later builds take about a
second. Each one's `build.log` has its last build's output.
`LIGHTLANG_MIRAGE_BUILD=0` skips the image.

```sh
light run examples/mirage_http_server.light              # prints its IP
light run examples/mirage_fetch.light -- --arg=<that IP>
```

`dev/mirage-check.sh` builds the examples (`examples/mirage_*.light`), boots
each image and checks its console and exit code, the network cases with one
unikernel serving and another fetching from it.

Lightlang's installed libraries can be required by their short name, as
Corelib's are (`sysinit/coqloadpath.ml`), so `Require Import Mirage.` finds
`Lightlang.Mirage`.

Not yet: DNS names (`fetch` takes an IP address), TLS, UDP, block devices
and key-value stores, and state shared between `serve` handlers.

## Reason: JSX components and apps

`theories/Lightlang/Reason.v` (not in the prelude) brings ReasonReact's JSX
to Lightlang, for components and apps that are checked, and can be proved
about, but not yet compiled to JavaScript.

```coq
Require Import Reason.

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

JSX is read by the lexer under `Set JSX Syntax`, which `Reason.v` exports
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
`examples/reason_counter.light` proves that a counter stays within its
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
`time` output) and `misc/bench-render` (`rocq-devtools` not built). The
unit tests need `ounit2`.

- `test-suite/success/gradual.v`: reduction rules in every machine, Ω, flag toggling
- `test-suite/success/gradual_vec.v`: indexed families (`vec`, `Fin`, `eq`): index checks, stuck casts on neutral indices, `match` on `?`
- `test-suite/output/Gradual.v`: the elaborated terms (cast insertion)
- `test-suite/misc/gradual_extraction.sh`: one program checked three ways. Each case's value holds as a syntactic normal form under `lazy`, `cbv`, `cbn`, `simpl` and `vm_compute`, and the extracted OCaml agrees with it, except for the documented differences, which are marked in `main.out`
- `test-suite/coqchk/gradual_register.v`, `test-suite/misc/gradual_rocqchk.sh`: `rocqchk` installs the rules of gradual primitives registered in the module it checks, and validates `Corelib.Gradual.Gradual` itself
