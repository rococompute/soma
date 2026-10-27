# Gradual coverage

How much of a typed program can be made less precise and still compile, and
does it still compute the same thing? Measured with `dev/gradual-lattice/` at
commit `8fe222a410`. The latest raw numbers are in
`dev/gradual-lattice/results/report.md`.

## The question

Lightlang gives up normalization, so a less precisely typed program is not
promised to be the same proof. What a programmer relies on, as with a Haskell
compiler, is:

1. **Static graduality.** If a program compiles, it still compiles after any
   type annotation is made less precise (replaced by `Dyn`, or a type inside
   it replaced by `Dyn`).
2. **Dynamic graduality.** Making a type less precise never changes what the
   program computes. A well-typed program has no source of `unk` or `raise`,
   so its results must stay exactly the same, not merely "less precise" or
   "an error".
3. **Compilation always answers.** Type checking can run code, so it may not
   terminate; the `Gradual Steps` budget turns that into an error. Outcomes
   are accepted, rejected, or out of steps.

The GCIC paper proves 1 and 2 for its calculus. This implementation, with
Rocq's elaborator, termination checker and implicit arguments, is not proven,
so we measure it.

## Method

- **Corpus.** Seven files of ordinary typed Rocq, 310 lines in total
  (`dev/gradual-lattice/corpus/`):
  - `arith.v`: arithmetic on `nat`;
  - `lists.v`: polymorphic and `nat` list functions, insertion sort;
  - `higher.v`: higher-order functions, pairs, options;
  - `records.v`: a record;
  - `expr.v`: an expression language and its evaluator;
  - `vectors.v`: length-indexed vectors;
  - `fmap.v`: a small library of finite maps as binary search trees
    (`add`, `find`, `remove` with `remove_min`, `fold`, `elements`,
    `map_values`, `of_list`, `counts`).

  Each file ends with **observations**: closed terms at fixed types,
  `Definition obs_… : T := …`.
- **Mutants.** For every type annotation (binders, `fun` binders, constructor
  arguments, return types), the whole file is compiled with that annotation
  replaced by `Dyn`, or with one base type inside it (`nat`, `bool`, a
  datatype of the file) replaced by `Dyn`. Further mutants replace every
  annotation of a definition, and every annotation of the file, at once. The
  other definitions are unchanged, so the callers of a mutated function must
  still compile.
- **Running.** Every file is compiled with gradual typing on
  (`rocq c -ri Corelib.Gradual.Gradual`). Each observation of a mutant that
  compiles is normalized (`Eval lazy`, fully printed) and compared with the
  original: same, less precise (`unk` where the original has a value),
  `raise`, or different.

290 mutants: 226 single-annotation, 57 whole-definition and 7 whole-file.

## Results

### Dynamic graduality: holds without exception

Across every run, every observation of every mutant that compiled has
exactly its original value:

| Observations of compiled mutants | Same | Less precise | `raise` | Different |
|---|---|---|---|---|
| final run (290 mutants) | 2134 | 0 | 0 | 0 |

One run did find a changed value, and the change that caused it was
narrowed before it was committed (see `d15787e665` below).

### Static graduality: 69% → 100%

Nothing ran out of steps or timed out. Each fix below was driven by the
rejections the harness reported.

| Step | Commit | Compiles |
|---|---|---|
| First measurement | `583e5e7162` | 143 / 208 (69%) |
| Casts from `Dyn` determine their arguments (`?` where nothing else does); `if` on `Dyn` casts to `bool` | `0626324252` | 152 / 208 (73%) |
| Recursion through `Dyn` is accepted without the termination check | `d011c4b1cf` | 193 / 208 (93%) |
| Implicit arguments that precision erased are `?` | `d15787e665` | 202 / 208 (97%) |
| Casts from `Dyn` also default arguments under constructors (`vec Dyn (S ?n)`) | `a5d7ea0db1` | 203 / 208 |
| In a match on a value of `Dyn`, a branch of another index is cast through `Dyn` | `bed62ca1f6` | 204 / 208 (98%) |
| `fmap.v` added to the corpus | `842eb1a60f` | 282 / 290 before the fix, 284 / 290 after |
| At `Dyn`, an application is inferred from its arguments first | `5942c46eb3` | 284 / 290 (98%) |
| Leftover implicits of a term that uses the primitives are `?` | `dd96446eae` | 289 / 290 |
| The return clause picks the index of a scrutinee of `Dyn` | `8fe222a410` | 290 / 290 (100%) |

Causes of rejection on the original six files, at the first measurement and
now:

| Cause | First | Now |
|---|---|---|
| Structural recursion on an argument of type `Dyn` (`Fixpoint fact (n : Dyn)`) | 32 | 0 |
| A recursive call through a constructor field made `Dyn` (`Plus (a : Dyn) …`, then `eval a`) | 8 | 0 |
| A type parameter or index left undetermined | 14 | 0 |
| A dependent match on a cast to an indexed family | 8 | 0 |
| `match`/`if` on a value of type `Dyn` | 3 | 0 |

By file and by kind of mutant (final run):

| File | Mutants | Compile | Observations (all same) |
|---|---|---|---|
| `arith.v` | 30 | 30 | 240 |
| `expr.v` | 20 | 20 | 60 |
| `fmap.v` | 82 | 82 | 738 |
| `higher.v` | 64 | 64 | 512 |
| `lists.v` | 56 | 56 | 448 |
| `records.v` | 16 | 16 | 48 |
| `vectors.v` | 22 | 22 | 88 |

| Kind | Compile | Rejected |
|---|---|---|
| one annotation | 226 | 0 |
| all annotations of a definition | 57 | 0 |
| all annotations of a file | 7 | 0 |

### What changed to get there

- **Undetermined arguments of casts from `Dyn`** (`0626324252`,
  `a5d7ea0db1`). `snd p` with `p : Dyn` left the other component's type
  unsolved, and `match v with vnil => …` with `v : Dyn` left the vector's
  length unsolved. Such arguments are now `?`: `Dyn` for types, `unk` for
  indices, also under constructors (`vec Dyn (S ?n)`). Indices are
  defaulted only in matches without a return clause: under a dependent
  return clause, an `unk` index changed `vhead`'s value. A `Dyn` condition
  of `if` is cast to `bool`.
- **Recursion through `Dyn`** (`d011c4b1cf`, `842eb1a60f`). GCIC^G has
  already given up termination, so the termination check has nothing to
  guarantee for recursion through `Dyn`.
  - Under Gradual Typing, a `Fixpoint` that uses gradual casts and fails the
    check is accepted without it, with a `gradual-unguarded-fixpoint` warning.
    `Print Assumptions` lists it as assumed guarded.
  - It recurses on its first possible argument of type `Dyn`, or else its
    first of an inductive type. Taking a type parameter, as before
    `842eb1a60f`, made the kernel reject the declaration.
  - In every reduction machine, fixpoints unfold on values of `Dyn`, and each
    such unfolding counts against the step budget, so a loop through `Dyn`
    stops with an error instead of hanging.
  - Fixpoints without gradual casts are checked as before.
  - The kernel accepts recursion on a `Dyn` argument only for such
    declarations; Rocq's own test for bug 15621 guards the rest.
- **Implicit arguments that precision erased** (`d15787e665`). After
  `map {A B} (f : Dyn) (l : Dyn)`, the type of `map` no longer mentions `A`
  or `B`, so no call can infer them. An implicit argument whose binder
  occurs nowhere in the rest of the type is `?`. `Definition x := nil.` is
  still rejected, with Gradual Typing on and off: `A` occurs in `list A`.
- **Dependent matches on a value of `Dyn`** (`bed62ca1f6`). In `vrep (n :
  Dyn)`, the branch `vnil : vec nat 0` is expected at `vec nat n`. When the
  scrutinee is a value of `Dyn`, a branch of the same family with
  consistent parameters is cast through `Dyn`. Ordinary matches are
  unchanged: `Fail Definition wrong_length : vec nat 1 := vnil` still
  fails.
- **Applications at `Dyn`** (`5942c46eb3`, found by `fmap.v`). With `add`'s
  tree made `Dyn`, `of_list`'s recursive call `add k v (of_list r)` is
  checked at `Dyn`. Unifying the result with `Dyn` first set `of_list`'s `V`
  to `Dyn` and cast `r`, so the call was no longer structural. Unifying with
  `Dyn` fixes nothing, so such an application is now inferred from its
  arguments first. Only when its arguments disagree (`cons 1 (cons true nil)
  : Dyn`) are its parameters `Dyn`.
- **Leftover implicits** (`dd96446eae`). Some implicits occur in the
  function's type but are reached by no argument and no expected type:
  `vmap {A B n} f (v : Dyn) : vec B n` called as `vsum (vmap f v3)`, where
  `vsum` takes any length; `find {V} k (t : Dyn) : option V` matched with
  `Some _`; `mem 3 (remove 3 t)` with `remove`'s tree made `Dyn`. Before a
  definition reports unresolved implicits, such an implicit is `?` when the
  term itself mentions `cast`, `unknown` or `err`, and the implicit does not
  occur in the type of the term. The same holds for the parameters and
  indices of a match scrutinee's type, so the index of
  `cast Dyn (vec Dyn ?n) v` in `vhead` with every annotation `Dyn` is `?`.
  User holes are left alone. `Definition x := nil.` and
  `let y := nil in 0` mention no primitive and stay rejected.
- **The return clause picks the index** (`8fe222a410`). In `vhead {A n}
  (v : Dyn) : A`, the match `return match m with 0 => unit | S _ => A end`
  is on `cast Dyn (vec Dyn ?n) v`. In a match with a return clause on a
  value of `Dyn`, an index that nothing determined is set to the one
  constructor, with `?` arguments, at which the return clause is
  consistent with the expected type. Here only `S` gives `A`, so the
  scrutinee is a `vec Dyn (S unk)`, the match has type `A`, and `vhead`
  returns the head itself. If no constructor or several fit (at expected
  type `Dyn`, both do), the index is left alone. Indices under a return
  clause are never defaulted to `unk`, which is what changed `vhead`'s
  value in an earlier attempt.

The full test suite is unchanged through these: 2751 pass, 3 environmental
failures (`latex1`, `timing-per-file`, `bench-render`).

## 290 of 290

At `8fe222a410`, every mutant compiles and every observation of every
mutant has exactly its original value: no `unk`, no `raise`, no stuck
cast. The two rules above closed the last six. The kernel needed no new
reduction rule: no observation was left as a stuck `cast Dyn nat 1`.

## Caveats

- **The corpus is small and hand-written.** Seven files, 310 lines. The
  numbers say where the implementation breaks, not how often real code does.
  `fmap.v`, the first library-shaped file, found one new bug (the recursive
  argument of an unguarded fixpoint) and one loss of precision (applications
  at `Dyn`). 290 of 290 is a statement about this corpus.
- **Observations are evaluated by the kernel's `lazy`.** The three-way
  extraction test (`test-suite/misc/gradual_extraction.sh`) separately
  checks that the other reduction machines and the extracted OCaml agree
  with it.
- **Single annotations are mutated, plus whole definitions and whole
  files.** Arbitrary combinations of annotations within a file are not.

## Reproducing

```sh
eval $(opam env --switch=. --set-switch)
dev/gradual-lattice/lattice.py --jobs 8    # a few seconds
cat dev/gradual-lattice/results/report.md
```
