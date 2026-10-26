# Finish the mutant suite

As of `73ee681647`. `dev/gradual-lattice/` is 284 of 290 mutants
compiling. All 2100 observations of those mutants have their original
value. Nothing runs out of steps. This file is how to get to 290 of
290 with that dynamic result intact.

`GROK_GRADUAL.md` is the earlier list. The implicits that no longer
occur in the function type, the index under `S`, and the branch cast
through `Dyn` have landed (`d15787e665`, `a5d7ea0db1`, `bed62ca1f6`).
Do not redo them. `gradual-coverage.md` is the measurement; the raw
failures are `dev/gradual-lattice/results/report.md`.

Done means `dev/gradual-lattice/lattice.py --jobs 8` prints 290
compiled, 0 rejected, and every observation `same`. A result of
`unk`, `raise`, a stuck cast, or any other term is not a pass. Do not
change the comparison in `lattice.py`.

## The six

| Mutant | What is left unsolved |
|---|---|
| `fmap.v` `find`, binder `tree V` replaced by `Dyn` | `mem` matches `find k (cast (tree V) Dyn t)` with `Some _`. `V` occurs in `option V`, and the wildcard does not determine it. |
| `fmap.v` `remove`, binder `tree V` replaced by `Dyn` | `mem 3 (remove 3 (cast (tree bool) Dyn sample))`. `mem`'s `V` is never `bool`, because the tree was cast to `Dyn` first. |
| `vectors.v` `vmap`, binder `vec A n` replaced by `Dyn` | `vsum (vmap f (cast (vec nat 3) Dyn v3))`. `vmap`'s `n` occurs in `vec B n`. `vsum` accepts any length, so nothing solves it. |
| `vectors.v` `vhead`, both annotations `Dyn` | The body is already a cast to `Dyn`. The index `?n` of `cast Dyn (vec Dyn ?n) v` is unsolved. Indices are not defaulted here: the match has a return clause (`GradualTyping.index_defaulting`). |
| `vectors.v`, every annotation in the file | The same `vhead` term. Fixing `vhead` unblocks it. If the next error is another implicit of this shape, it is the same rule, not a new cause. |
| `vectors.v` `vhead`, binder `vec A (S n)` replaced by `Dyn` | Not an unsolved implicit. The match typechecks at `match ?n with 0 => unit \| S _ => A` and the function must return `A`. Those are not consistent, so no cast is inserted. Defaulting that index to `unk` is what made `vhead` return `cast Dyn nat 1` instead of `1` (`d15787e665`). Do not turn `index_defaulting` back on for every return clause. |

`arith.v`, `expr.v`, `higher.v`, `lists.v`, and `records.v` are
already clean. `Fail Definition no_type := nil` and
`Fail Definition wrong_length` in `test-suite/success/gradual.v` stay
rejected.

## 1. A leftover implicit, and the term already uses `Dyn`

The five unsolved-implicit mutants fail in
`check_evars_are_solved` (`vernac/declare.ml`), which prints
"unresolved implicit arguments". The implicit occurs in the function's
type, so the check in `pretype_app` (`noccurn` on the rest of the
product, `d15787e665`) does not fire. Nothing downstream solves it
either.

Under Gradual Typing, before that check reports failure, instantiate
a leftover `Evar_kinds.ImplicitArg` with `unknown` of its type when
both of these hold:

- The term being checked already contains `cast`, `unknown`, or
  `err`. `GradualTyping.uses` is that walk. `Definition x := nil`
  contains none, so `A` stays unsolved.
- The evar does not occur in the type of that term. For
  `obs_vsum : nat` the length is not in `nat`. For `mem : bool` the
  value type is not in `bool`. For `nil` the evar occurs in
  `list A`, so it is not instantiated even if a cast were added
  beside it.

Do not instantiate any other evar kind. Do not instantiate an
implicit that occurs in the ascribed type. Do not run this with
Gradual Typing off.

`let y := nil in 0` mentions no gradual primitive, so it stays
rejected. Add that next to `no_type` in `test-suite/success/gradual.v`.

Add one positive test for each shape, with the value the precise
program has:

- `mem` on a `find` whose tree argument is `Dyn`, ignoring the
  payload of `Some`, result `true` or `false` as in `obs_mem`.
- `vsum (vmap f v)` with `v : Dyn`, result the mapped sum.
- `vhead` with both annotations `Dyn`, applied to a concrete vector,
  result the head. This is the one that can come out as
  `cast Dyn nat 1`. If it does, do not update the expected value.
  Section 3 is for that term.

Rerun the lattice. The five should compile. Every observation that
already compared equal must stay equal, including `obs_find`,
`obs_mem`, `obs_remove`, `obs_vsum`, and `obs_vhead`. The binder-only
`vhead` mutant is still rejected here. That is section 2.

## 2. The return clause picks the index

`vhead {A n} (v : Dyn) : A` still has

```coq
match v in vec _ m return match m with 0 => unit | S _ => A end with
| vnil => tt | vcons x _ => x end
```

The scrutinee is cast to `vec Dyn ?n` and `?n` is left alone because
there is a return clause (`Cases.compile_cases`,
`with_index_defaulting (Option.is_empty predopt)`). The `S` branch
returns `A` and the `O` branch returns `unit`. The function's type
asks for `A`, so only one index shape typechecks: `S _`.

After the return predicate is built in `compile_cases`, for a
scrutinee that `set_gradual_scrutinee` marked, try each constructor of
an unsolved index. Instantiate it with `unknown` at every argument
(`S unk`, and `O` which has none). Keep the candidate when the
predicate applied to it converts with the expected type, or is
consistent with it under Gradual Typing. If exactly one constructor
survives, use it. If none or several do, leave the index alone.

For this `vhead` the only survivor is `S`. The cast target is
`vec Dyn (S unk)`. `match (S unk) with 0 => unit | S _ => A` reduces
to `A`, so the match's type is `A` and no cast is wrapped around it.
The `vcons` branch returns `cast Dyn A x`. On a real vector, `x` is
`cast nat Dyn` of the head, and that cast back is the head. The `vnil`
branch is not taken.

Both constructors survive when the expected type is `Dyn` (the
all-annotations mutant). Do not guess. Section 1 sets that leftover
index when the body is accepted as a cast to `Dyn`.

Replace `Fail Definition vhead_dyn` with a definition of that shape
and `Goal vhead_dyn (vcons 1 (vcons 2 (vcons 3 vnil)) : Dyn) = 1`.
`wrong_length` stays a `Fail`: its scrutinee is a `vnil`, not a value
of `Dyn`.

Rerun the lattice. This mutant should compile, and `obs_vhead` on it
should be `1`, the same term as the precise program.

## 3. Only if a value is still `cast Dyn nat 1`

Section 1 on the all-annotations `vhead` can leave

```text
cast Dyn nat 1
```

as the normal form of `obs_vhead`. That is the term `d15787e665`
refused. It is stuck because `reduce_cast` (`kernel/gradual.ml`)
returns `None` for an unknown source and a constructor
(`TConstruct`). The injected form `cast Dyn nat (cast nat Dyn 1)`
already reduces to `1`.

If, and only if, the lattice prints that stuck cast (or the same
shape at another type) for an observation:

- In the kernel, `cast Dyn B v` reduces to `v` when `v` is a
  constructor of `B`, and to `err` when it is a constructor of a
  different head. Arguments of the constructor are cast the way
  `cast_constructor` already casts them. A neutral term stays stuck.
- The same rule in `plugins/extraction/gradual_rt.ml`. A row in
  `test-suite/misc/gradual_extraction/` for `cast Dyn nat 1` reducing
  to `1`, and for `cast Dyn nat true` raising. The three-way test
  stays at 0 disagreements outside the rows it already marks.
- Rerun the lattice. `obs_vhead` is then `1`. If some other
  observation changes, the rule is too wide. Restrict it to a
  constructor whose inductive is `B`, and if a value still moves,
  drop the rule and record the mutant in `gradual-coverage.md`
  instead of forcing 290.

Do not add this rule if section 1 already prints `1`.

## Check

```sh
dune build rocq-runtime.install
make -C test-suite success/gradual.v.log
dev/gradual-lattice/lattice.py --jobs 8
```

Section 1 edits `vernac/declare.ml`, which runs on every definition.
The new branch is under `GradualTyping.enabled`, so the flag-off suite
does not take it. Run `make -C test-suite` once after that edit
anyway. The recorded result is 2751 passed and 3 environmental
failures (`latex1`, `timing-per-file`, `bench-render`). A new failure
there is a gate that is not actually off.

Section 3 also runs `make -C test-suite misc/gradual_extraction.sh`.

Then add a paragraph to `gradual-coverage.md`: 290 of 290, the two
rules, and the commit. The dynamic table stays all `same`.

## Leave these alone

- `index_defaulting` for matches with a return clause. Section 2
  chooses one constructor from the expected type. It does not default
  every index to `unk`.
- `Definition x := nil` and `let y := nil in 0`, with the flag on and
  off.
- `wrong_length`.
- The dynamic comparison. Do not score `unk`, `raise`, or a stuck
  cast as the original value.
- Germs, a `Dyn@{i}` hierarchy, VM and native rules, and boxing
  `Extract Inductive` types.
