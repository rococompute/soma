# Gradual Rocq: GCIC^G, the variant that gives up normalization

This fork of the Rocq Prover (based on 9.3.0) adds **gradual dependent
types**, following

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

Definition delta := fun x : Dyn => x x.
Definition omega : Dyn := delta delta.   (* well typed *)
Eval lazy in omega.                      (* loops forever *)
```

Because conversion can run arbitrary computation, **type checking is
undecidable**. `Check (eq_refl : omega = unk)` diverges.

## Quick start

```sh
opam switch create ./ ocaml-base-compiler.4.14.2 --no-install
opam install --switch=. dune ocamlfind zarith
eval $(opam env --switch=. --set-switch)
make dunestrap
dune build rocq-runtime.install coq-core.install rocq-core.install
_build/install/default/bin/rocq c my_file.v
```

```coq
From Corelib.Gradual Require Import Gradual.   (* also sets Gradual Typing *)

Definition succ_dyn (x : Dyn) : nat := x + 1.
Print succ_dyn.
(* succ_dyn = fun x : Dyn => cast Dyn nat x + 1 *)

Compute succ_dyn 41.     (* = 42 *)
Compute succ_dyn true.   (* = raise : nat, a runtime type error *)

Definition apply3 (g : Dyn) : nat := g 3.
(* elaborates to: cast Dyn nat (cast Dyn (Dyn -> Dyn) g (cast nat Dyn 3)) *)
Compute apply3 S.        (* = 4 *)
Compute apply3 negb.     (* = raise *)

Compute 2 + unk.         (* = S (S unk) *)
Compute (unk : nat -> bool).  (* = fun _ => unk *)

Fail Definition bad : nat := true.  (* still a static error: not consistent *)
```

| Surface syntax | Meaning (paper notation) |
|---|---|
| `Dyn` | the unknown type `?_□` (abbreviation for `unknown Type`) |
| `unk` | the unknown term `?_A` at the expected type `A` |
| `raise` | the error `err_A` at the expected type |
| `cast A B t` | the cast `⟨B ⇐ A⟩ t` |
| `Set/Unset Gradual Typing` | turns consistency-based elaboration on or off |

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

### Reduction rules (`kernel/gradual.ml`)

`A`, `B` are in weak head normal form. "Germ-free": a value of type `?` is
`cast A Dyn t`, where `A` is the original head type.

| Redex | Reduct |
|---|---|
| `unknown (forall x:A, B)` | `fun x:A => unknown B` (same for `err`) |
| `match unknown (I pars idx) return P with … end` | `unknown (P idx (unknown (I pars idx)))` (same for `err`) |
| `fix f … (unknown I) …` | unfolds, like a constructor (then hits the rule above) |
| `(unknown R).(p)` (primitive projection) | `unknown (type of p)` |
| `cast A A t` (syntactically equal) | `t` |
| `cast (err _) B t`, `cast A (err _) t` | `err B` |
| `cast Dyn Dyn t` | `t` |
| `cast Dyn B (cast A Dyn t)` | `cast A B t` |
| `cast A Dyn (unknown _)` / `cast Dyn B (unknown _)` | `unknown B` (same for `err`) |
| `cast (forall x:A1, B1) (forall x:A2, B2) f` | `fun x:A2 => cast B1[x'/x] B2 (f x')` where `x' := cast A2 A1 x` |
| `cast (Sort s1) (Sort s2) T` | `T` if `s1 ≤ s2` by family (Prop ≤ Set ≤ Type), else `err` |
| `cast (I p1) (I p2) (c p1 args)` | `c p2 (cast Tᵢ[p1] Tᵢ[p2] argsᵢ)` |
| `cast (I p1 i1) (I p2 i2) (c …)` (indexed) | as above, if the indices the constructor produces are compatible with `i2` (`?` matches anything), else `err` |
| `cast (I …) (I …) (unknown _)` | `unknown B` (same for `err`) |
| any other head clash among Π / Sort / inductive | `err B` |
| anything involving a neutral type | stuck |

The GCIC^G decision is in the injection rule `cast A Dyn t`. It keeps `A`
as is and never lowers the universe of a Π germ, so `Dyn -> Dyn : Type@{i}`
whenever `Dyn : Type@{i}`.

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

- a term `t : A` where `B` is expected, with `A ~ B` consistent, becomes `cast A B t`;
- a term `f : Dyn` in function position becomes `cast Dyn (Dyn -> Dyn) f`;
- a term `T : Dyn` in type position becomes `cast Dyn Type T`.

## Extraction to OCaml

Extraction erases types, which casts need. So OCaml extraction compiles
each `cast A B t` to a call to a small runtime, `Gradual_rt`
(`plugins/extraction/gradual_rt.ml`), with runtime descriptions of `A`
and `B`. The runtime applies the rules above. The extracted file embeds the
runtime: it only needs the OCaml standard library, so it also builds for
MirageOS unikernels.

```coq
Definition succ_dyn (x : Dyn) : nat := x + 1.
Extraction succ_dyn.
(* let succ_dyn x =
     add (Gradual_rt.cast_with ... Gradual_rt.unknown_ty
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil) x)
       (succ 0) *)
```

- A value of type `Dyn` is the value plus the description of its type.
- A cast between function types wraps the function. The wrapper makes a
  tail call when the codomain needs no cast, so Ω loops in constant stack.
- For each inductive type, extraction generates a match on its
  constructors that casts their arguments and checks the indices. It
  therefore works with `Extract Inductive` (e.g. `nat => int`).
- A failed cast, or reaching `raise`, raises `Gradual_rt.Cast_error`. The
  extracted `.mli` exports it.
- **Type parameters** that casts need are passed at run time. A parameter
  is needed when it occurs in the types of a cast, `unknown` or `err`, or in
  an argument for a needed parameter of another function, including
  recursive calls. The constant then takes the type's description as an
  argument and its callers pass it:

  ```coq
  Definition to_dyn {A : Type} (x : A) : Dyn := x.
  (* val to_dyn : __ -> 'a1 -> __
     let to_dyn a x = Gradual_rt.cast_with ... a Gradual_rt.unknown_ty x *)
  ```

  Other type parameters are erased as usual, so code without casts is
  extracted as before.
- The test is `test-suite/misc/gradual_extraction.sh`. The MirageOS on
  Apple Silicon test matrix runs the same program as an `hvt` unikernel.

Extraction differs from the kernel in these ways:

- **Only the type parameters of constants are passed.** A cast at a type
  variable bound elsewhere (a local `fun (A : Type) => …`, a type stored in
  a constructor) is rejected at extraction time. So is a function that
  needs type parameters at run time used without them, for example
  `@to_dyn` passed to a function expecting `forall A, A -> Dyn`: the
  callee would not pass the description.
- **A failed cast raises at once**, also inside data: the kernel computes
  `cons raise nil`, where the extracted code raises.
- **`?_A` at an inductive type raises `Gradual_rt.Unknown_term`** when it is
  evaluated. Extracted code is call-by-value and has no value for it, so
  `2 + unk` raises, where the kernel computes `S (S unk)`. At function types
  `unk` is `fun _ => unk`, as in the kernel, and `unk : Dyn` is a value.
- **Proofs are erased**, so casts between propositions are not checked.
- **Coinductive types** are not supported in casts yet.
- Only OCaml is supported. Haskell and Scheme extraction print an error.

## Limitations and known gaps

- **No mechanized proofs.** Graduality and conservativity come from the
  design (typing untouched, rules follow the paper). They are not proven
  for this implementation.
- **Germ-free casts.** The paper factors injections through *germs* (`? -> ?`,
  `I ? … ?`). This fork injects the original head type directly. In GCIC^G
  this should be observationally equivalent, and it avoids universe
  arithmetic in the kernel.
- **Universe levels are not checked by casts between sorts.** Only sort
  families are compared, since the reduction machines do not have the
  universe graph. Everything casted lives below the single global universe
  `Corelib.Gradual.Gradual.gradual`.
- **SProp** is not supported, because the axioms quantify over `Type`.
- **Indexed families** go beyond the paper, which only treats parameters.
  The behaviour is a pragmatic first-order index check.
- **VM / native compilation** treat the axioms as opaque. Under
  `Gradual Typing`, `vm_compute`, `native_compute` and `Compute` fall back
  to `cbv`.
- **Reducts of `match` on `?` may live above `gradual`** when the match
  returns a large type. This is harmless for computation, but such a
  reduct would not re-typecheck.
- **Bidirectionality is checking, not synthesis.** With an expected
  type, argument inference is delayed until that type has been unified
  with the result, so `cons 1 (cons true nil) : list Dyn` checks both
  elements at `Dyn`. Leading type arguments are still inferred first, so
  an explicit one wins over the expected type: `@cons Dyn 1 nil : list nat`
  is a cast from `list Dyn`. An ascription of `Dyn` does not determine
  constructor parameters, so `cons 1 (cons true nil) : Dyn` is still
  rejected. Write `list Dyn`, or `@cons Dyn 1 …`.

## Tests

- `test-suite/success/gradual.v`: reduction rules in every machine, Ω, flag toggling
- `test-suite/output/Gradual.v`: the elaborated terms (cast insertion)
- `test-suite/misc/gradual_extraction.sh`: extracted code, compiled and run, agrees with the kernel
