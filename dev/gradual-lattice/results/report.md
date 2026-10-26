# Graduality lattice

290 mutants of 7 files.

| Static: mutant | count |
|---|---|
| compiled | 284 |
| rejected | 6 |
| out_of_steps | 0 |
| timeout | 0 |

| Dynamic: observation of a compiled mutant | count |
|---|---|
| same | 2100 |
| less_precise | 0 |
| raise | 0 |
| different | 0 |

| Mutants by kind | compiled | rejected | out of steps | timeout |
|---|---|---|---|---|
| single | 222 | 4 | 0 | 0 |
| definition | 56 | 1 | 0 | 0 |
| file | 6 | 1 | 0 | 0 |

| Why mutants are rejected | count |
|---|---|
| an implicit argument that nothing determines (no argument or expected type fixes it) | 5 |
| dependent match on a cast to an indexed family (index or return type not inferred) | 1 |

## Mutants that do not compile

- `fmap.v` find: binder whole (line 10) tree V -> Dyn: **rejected** (an implicit argument that nothing determines (no argument or expected type fixes it)) — Error: The following term contains unresolved implicit arguments: (fun (V : Type) (k : nat) (t : tree V) => match find k (cast (tree V) Dyn t) with | Some _ => true | None => false end) More precisely: - ?V: Cannot infer the implicit parameter V of find whose type is "Type" in environment: V : Type 
- `fmap.v` remove: binder whole (line 43) tree V -> Dyn: **rejected** (an implicit argument that nothing determines (no argument or expected type fixes it)) — Error: The following term contains unresolved implicit arguments: (mem 3 (remove 3 (cast (tree bool) Dyn sample))) More precisely: - ?V: Cannot infer the implicit parameter V of mem whose type is "Type".
- `vectors.v` vhead: binder whole (line 8) vec A (S n) -> Dyn: **rejected** (dependent match on a cast to an indexed family (index or return type not inferred)) — Error: In environment A : Type n : nat v : Dyn The term "match cast Dyn (vec Dyn ?n) v in vec _ m return match m with | 0 => unit | S _ => A end with | vnil => tt | vcons x _ => cast Dyn A x end" has type "match ?n with | 0 => unit | S _ => A end" while it is expected to have type "A". No cast was i
- `vectors.v` vhead: all 2 annotations -> Dyn: **rejected** (an implicit argument that nothing determines (no argument or expected type fixes it)) — Error: The following term contains unresolved implicit arguments: (fun (A : Type) (n : nat) (v : Dyn) => cast match ?n with | 0 => unit | S _ => A end Dyn match cast Dyn (vec Dyn ?n) v in vec _ m return match m with | 0 => unit | S _ => A end with | vnil => tt | vcons x _ => cast Dyn A x end) More p
- `vectors.v` vmap: binder whole (line 12) vec A n -> Dyn: **rejected** (an implicit argument that nothing determines (no argument or expected type fixes it)) — Error: The following term contains unresolved implicit arguments: (vsum (vmap (fun x : nat => x * 10) (cast (vec nat 3) Dyn v3))) More precisely: - ?n: Cannot infer the implicit parameter n of vmap whose type is "nat".
- `vectors.v` all 13 annotations of the file -> Dyn: **rejected** (an implicit argument that nothing determines (no argument or expected type fixes it)) — Error: The following term contains unresolved implicit arguments: (fun (A : Type) (n : nat) (v : Dyn) => cast match ?n with | 0 => unit | S _ => A end Dyn match cast Dyn (vec Dyn ?n) v in vec _ m return match m with | 0 => unit | S _ => A end with | vnil => tt | vcons x _ => cast Dyn A x end) More p
