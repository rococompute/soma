# Graduality lattice

208 mutants of 6 files.

| Static: mutant | count |
|---|---|
| compiled | 204 |
| rejected | 4 |
| out_of_steps | 0 |
| timeout | 0 |

| Dynamic: observation of a compiled mutant | count |
|---|---|
| same | 1380 |
| less_precise | 0 |
| raise | 0 |
| different | 0 |

| Mutants by kind | compiled | rejected | out of steps | timeout |
|---|---|---|---|---|
| single | 159 | 2 | 0 | 0 |
| definition | 40 | 1 | 0 | 0 |
| file | 5 | 1 | 0 | 0 |

| Why mutants are rejected | count |
|---|---|
| an implicit argument that nothing determines (no argument or expected type fixes it) | 3 |
| dependent match on a cast to an indexed family (index or return type not inferred) | 1 |

## Mutants that do not compile

- `vectors.v` vhead: binder whole (line 8) vec A (S n) -> Dyn: **rejected** (dependent match on a cast to an indexed family (index or return type not inferred)) — Error: In environment A : Type n : nat v : Dyn The term "match cast Dyn (vec Dyn ?n) v in vec _ m return match m with | 0 => unit | S _ => A end with | vnil => tt | vcons x _ => cast Dyn A x end" has type "match ?n with | 0 => unit | S _ => A end" while it is expected to have type "A". No cast was i
- `vectors.v` vhead: all 2 annotations -> Dyn: **rejected** (an implicit argument that nothing determines (no argument or expected type fixes it)) — Error: The following term contains unresolved implicit arguments: (fun (A : Type) (n : nat) (v : Dyn) => cast match ?n with | 0 => unit | S _ => A end Dyn match cast Dyn (vec Dyn ?n) v in vec _ m return match m with | 0 => unit | S _ => A end with | vnil => tt | vcons x _ => cast Dyn A x end) More p
- `vectors.v` vmap: binder whole (line 12) vec A n -> Dyn: **rejected** (an implicit argument that nothing determines (no argument or expected type fixes it)) — Error: The following term contains unresolved implicit arguments: (vsum (vmap (fun x : nat => x * 10) (cast (vec nat 3) Dyn v3))) More precisely: - ?n: Cannot infer the implicit parameter n of vmap whose type is "nat".
- `vectors.v` all 13 annotations of the file -> Dyn: **rejected** (an implicit argument that nothing determines (no argument or expected type fixes it)) — Error: The following term contains unresolved implicit arguments: (fun (A : Type) (n : nat) (v : Dyn) => cast match ?n with | 0 => unit | S _ => A end Dyn match cast Dyn (vec Dyn ?n) v in vec _ m return match m with | 0 => unit | S _ => A end with | vnil => tt | vcons x _ => cast Dyn A x end) More p
