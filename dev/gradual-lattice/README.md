# Graduality lattice

`lattice.py` measures whether gradual Rocq keeps the two promises of
graduality on real programs:

- **static**: making a type annotation less precise never turns a program
  that compiles into one that does not;
- **dynamic**: it never changes what the program computes. A well-typed
  program has no source of `unk` or `raise`, so every observation must keep
  exactly its value.

`corpus/` holds ordinary typed programs (arithmetic, lists, higher-order
functions, options, a record, an expression evaluator, length-indexed
vectors, and a small library of finite maps as search trees). Each file ends with observations, `Definition obs_… : T := …`, at
fixed types. For every type annotation (binders, `fun` binders, constructor
arguments, return types) the harness compiles the whole file with that
annotation made less precise: replaced by `Dyn`, or with one base type inside
it replaced (`list nat` → `list Dyn`). It also compiles the file with all
annotations of a definition, or of the whole file, replaced by `Dyn`. Files
are compiled with gradual typing on (`rocq c -ri Corelib.Gradual.Gradual`),
and the observations are evaluated (`Eval lazy`) and compared with the
original.

```sh
dev/gradual-lattice/lattice.py            # all of corpus/, results in results/
dev/gradual-lattice/lattice.py --jobs 8 corpus/lists.v
```

`results/report.md` gives the counts, why each rejected mutant is rejected,
and every observation that changed; `results/results.json` has the details.
A mutant compiles, is rejected, runs out of `Gradual Steps`, or times out.
An observation is the same, less precise (`unk` where the original has a
value), `raise`, or different.

To add programs, put a typed `.v` file in `corpus/` that compiles with
gradual typing on, with its observations named `obs_…`.
