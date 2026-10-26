# How to proceed from the graduality lattice

Reviewed `gradual-coverage.md` against `dev/gradual-lattice/results/report.md`
and the tree at `10fa5bf53d`. The note matches the run. 208 mutants, 193
compile, 15 do not, nothing runs out of steps. Every one of the 1320
observations of a compiled mutant has its original value.

`GROK_PLAN.md` is done (the `: Dyn` comment, match propagation in
extraction, the array row). This file is the work list now.

The lattice is the right test. Static graduality is "a typed program
still compiles after an annotation becomes `Dyn`". Dynamic graduality
is "an observation keeps its exact value", because these programs have
no source of `unk` or `raise`. Do not relax the dynamic check to accept
`unk`, `raise`, or a stuck cast as close enough.

## What the 15 actually are

`arith.v`, `expr.v`, `higher.v`, and `records.v` compile under every
mutant. The failures are four polymorphic list functions and the
vectors.

Six of them are a single annotation. The other nine replace every
annotation of one definition, or of the file. The harness labels 13 as
"type parameter left undetermined by a cast from Dyn" because the error
text matches `Cannot infer the implicit parameter` or
`unresolved implicit arguments` (`dev/gradual-lattice/lattice.py`).
That label covers two different situations.

**Parameters that the mutated type no longer mentions (12).**
`map {A B} (f : Dyn) (l : Dyn) : Dyn` has a type `Type -> Type -> Dyn
-> Dyn -> Dyn`. `A` and `B` occur in none of the argument types and in
none of the result. The recursive call `map f r`, and the unchanged
caller `obs_map`, have nothing to unify them with. The same shape is
`filter`, `fold`, `vhead` with both annotations replaced, `vmap`,
`vsum`, `to_list`, and both whole-file mutants. `vhead` with only the
vector binder replaced is the index version: the type is
`forall A n, Dyn -> A`, the result still determines `A`, and `n` occurs
nowhere.

**An evar under a constructor in a cast from `Dyn` (1).**
`v3 : Dyn`, then `vhead v3`. The elaborated term in the report is
`vhead (cast Dyn (vec nat (S ?n)) v3)`. `A` was solved as `nat`. `n`
was not, and it sits under `S`, so `default_args_to_unknown` in
`pretyping/gradualTyping.ml` does not see it. That function only
replaces an inductive argument that is itself an evar.

**Dependent matches (2).** These are not an implicit-argument bug.

- `vmap` with `v : Dyn`. The function still returns `vec B n`. The
  `vnil` branch has type `vec B 0`. Rocq expects `vec B n` and does not
  refine `n`, because the scrutinee is a cast, not a vector. `0` and
  `n` are not consistent, so no cast is inserted.
- `vrep` with `n : Dyn`. The return type is `vec nat (cast Dyn nat n)`.
  In the `O` branch the index is `cast Dyn nat ?u@{n1:=0}`. That cast
  is stuck: `reduce_cast` in `kernel/gradual.ml` gives `None` for an
  unknown source and a constructor or a neutral term. `vec nat 0` is
  not consistent with it.

## 1. Default an implicit that precision erased

Do this first. It is the bulk of the gap, and it does not need a new
reduction rule.

When Gradual Typing is on, an `ImplicitArg` evar that is still
unsolved after the application has been elaborated is set to
`unknown` of its type, but only when it occurs neither in the expected
type of the application nor in the type of the constant outside
arguments whose type is `?`. `map`'s `A` and `B`, and `vhead`'s `n`
after the vector binder became `Dyn`, are that case.

The place is the end of elaboration of an application, before
`check_evars` and `check_extra_evars_are_solved` in
`pretyping/pretyping.ml`. Those two, and `check_evars_are_solved` in
`vernac/declare.ml`, are what reject the mutants. Instantiate the evar
there. Do not do it for every unsolved evar, and do not do it with
Gradual Typing off.

Do not restrict it to definitions whose own annotations mention `Dyn`.
`gradual-coverage.md` suggests that, and it is the wrong scope. The
whole-definition mutants are also required to keep their callers
compiling, and those callers are `obs_map` and `obs_vhead`. Their
annotations never mention `Dyn`. The trigger is the type of the
constant being applied.

`Definition x := nil` must stay rejected. `A` occurs in `list A`. Add
that as a `Fail` next to the new positive tests in
`test-suite/success/gradual.v`. Also add one recursive case taken from
the lattice, `map` with every annotation replaced by `Dyn`, called on
a concrete list, with the same value as the precise `map`.

Then rerun:

```sh
dev/gradual-lattice/lattice.py --jobs 8
```

Static count should move. Dynamic count must stay all `same`. The `v3`
mutant will still fail; that is the next paragraph. If a compiled
mutant changes an observation, the default fired on an evar something
else should have solved. Narrow the occurrence check. Do not keep the
rule and update the expected value.

## 2. The `v3` index under `S`

After 1, extend `default_args_to_unknown` so a cast from `Dyn` to
`vec nat (S ?n)` sets that inner evar to `unk`, not only an argument
that is the evar itself. Same bet the function already makes for a
bare argument: nothing else will determine it.

Rerun the lattice. `obs_vhead` on a `v3` whose type was replaced by
`Dyn` must stay `1`. The cast back from `Dyn` lands on
`vec nat (S unk)`, the index check accepts the real length, and the
head is the head. If some other observation changes, revert the walk
under constructors and leave this one mutant recorded. Twelve
compiling is enough to ship the rule from section 1 without it.

## 3. Dependent match, only with the lattice watching

Do this after 1 and 2, and be ready to stop.

`vmap` and `vrep` fail in match elaboration, not in implicit synthesis.
A branch whose type is not consistent with the expected type gets no
cast today, which is right for `nat` against `bool`. The new case is
narrow: the scrutinee's type is `?` or a cast from `?`, and the branch
type and the expected type are the same indexed family at indices that
are not consistent. Cast the branch through `Dyn`
(`cast (vec B 0) Dyn vnil`, then on to `vec B n`).

`vrep` will not fall out of a kernel change that reduces
`cast Dyn nat O`. The index in the error is
`cast Dyn nat ?u@{n1:=0}`, a pattern variable, and that is stuck for
the same reason any neutral is stuck.

The taken branch is the risk. `obs_vsum` runs `vmap` on a vector of
length 3, and `obs_vrep` runs `vrep 4 5`, so both take the successor
branch. If that branch also fails to convert and receives a cast
through `Dyn`, `Eval lazy` can get stuck on the index and the
observation changes. Run the lattice. If `obs_vsum` or `obs_vrep`
is no longer the original value, drop the branch cast and leave these
two mutants rejected. Write the stuck term into `gradual-coverage.md`.
Do not special-case the two definitions.

## 4. Then grow the corpus

Not before. A larger corpus now mixes new causes with these fifteen.
After 1, add one ordinary library development that does not import
`Gradual`: a self-contained file, observations named `obs_…` at closed
types, as `dev/gradual-lattice/README.md` describes. Rerun. New
rejections get a row in the cause table only when the regex is wrong
for them; `map`'s failure is "the parameter occurs nowhere", and the
current regex hides that behind "cast from Dyn". Fix the label when
you touch the harness.

Combinations of annotations inside one definition are not measured.
Whole-definition mutants already cover the strongest single-definition
case. Arbitrary subsets are the step after a library file, not the
next one.

## Leave these alone

- The dynamic check. 1320 of 1320 is the result worth protecting.
- `Definition x := nil`, with Gradual Typing on and off.
- Fixpoints that do not use a gradual primitive. They stay guarded.
  The `gradual-unguarded-fixpoint` path is for recursion through `Dyn`
  only (`d011c4b1cf`).
- A separate `Dyn@{i}`, germs, VM and native rules, and a
  mechanization. Same reasons as in `GROK_PLAN.md`.
- Boxing `Extract Inductive` types so extracted `bool` can hold
  `raise`.

## Check

```sh
dune build rocq-runtime.install
make -C test-suite success/gradual.v.log
dev/gradual-lattice/lattice.py --jobs 8
```

The full suite is recorded at `d011c4b1cf` (2751 passed, 3
environmental failures). Run it again if section 1 or 3 changes
`pretyping.ml`, because that code runs with Gradual Typing off on
every file in the suite. Section 2 is `gradualTyping.ml` and only
runs when the flag is on; the lattice plus `success/gradual.v` is the
check for it.
