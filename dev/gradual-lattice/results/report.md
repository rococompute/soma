# Graduality lattice

290 mutants of 7 files.

| Static: mutant | count |
|---|---|
| compiled | 289 |
| rejected | 1 |
| out_of_steps | 0 |
| timeout | 0 |

| Dynamic: observation of a compiled mutant | count |
|---|---|
| same | 2130 |
| less_precise | 0 |
| raise | 0 |
| different | 0 |

| Mutants by kind | compiled | rejected | out of steps | timeout |
|---|---|---|---|---|
| single | 225 | 1 | 0 | 0 |
| definition | 57 | 0 | 0 | 0 |
| file | 7 | 0 | 0 | 0 |

| Why mutants are rejected | count |
|---|---|
| dependent match on a cast to an indexed family (index or return type not inferred) | 1 |

## Mutants that do not compile

- `vectors.v` vhead: binder whole (line 8) vec A (S n) -> Dyn: **rejected** (dependent match on a cast to an indexed family (index or return type not inferred)) — Error: In environment A : Type n : nat v : Dyn The term "match cast Dyn (vec Dyn ?n) v in vec _ m return match m with | 0 => unit | S _ => A end with | vnil => tt | vcons x _ => cast Dyn A x end" has type "match ?n with | 0 => unit | S _ => A end" while it is expected to have type "A". No cast was i
