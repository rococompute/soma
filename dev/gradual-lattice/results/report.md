# Graduality lattice

208 mutants of 6 files.

| Static: mutant | count |
|---|---|
| compiled | 202 |
| rejected | 6 |
| out_of_steps | 0 |
| timeout | 0 |

| Dynamic: observation of a compiled mutant | count |
|---|---|
| same | 1372 |
| less_precise | 0 |
| raise | 0 |
| different | 0 |

| Mutants by kind | compiled | rejected | out of steps | timeout |
|---|---|---|---|---|
| single | 157 | 4 | 0 | 0 |
| definition | 40 | 1 | 0 | 0 |
| file | 5 | 1 | 0 | 0 |

| Why mutants are rejected | count |
|---|---|
| dependent match on a cast to an indexed family (index or return type not inferred) | 3 |
| type parameter left undetermined by a cast from Dyn | 3 |

## Mutants that do not compile

- `vectors.v` vhead: binder whole (line 8) vec A (S n) -> Dyn: **rejected** (dependent match on a cast to an indexed family (index or return type not inferred)) — Error: In environment A : Type n : nat v : Dyn The term "match cast Dyn (vec Dyn ?n) v in vec _ m return match m with | 0 => unit | S _ => A end with | vnil => tt | vcons x _ => cast Dyn A x end" has type "match ?n with | 0 => unit | S _ => A end" while it is expected to have type "A". No cast was i
- `vectors.v` vhead: all 2 annotations -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: The following term contains unresolved implicit arguments: (fun (A : Type) (n : nat) (v : Dyn) => cast match ?n with | 0 => unit | S _ => A end Dyn match cast Dyn (vec Dyn ?n) v in vec _ m return match m with | 0 => unit | S _ => A end with | vnil => tt | vcons x _ => cast Dyn A x end) More p
- `vectors.v` vmap: binder whole (line 12) vec A n -> Dyn: **rejected** (dependent match on a cast to an indexed family (index or return type not inferred)) — Error: In environment vmap : forall (A B : Type) (n : nat), (A -> B) -> Dyn -> vec B n A : Type B : Type n : nat f : A -> B v : Dyn The term "vnil" has type "vec B 0" while it is expected to have type "vec B n" (cannot unify "0" and "n"). No cast was inserted: the types are not consistent, "0" and "
- `vectors.v` vrep: binder whole (line 18) nat -> Dyn: **rejected** (dependent match on a cast to an indexed family (index or return type not inferred)) — Error: In environment vrep : forall n : Dyn, nat -> vec nat (cast Dyn nat n) n : Dyn x : nat The term "vnil" has type "vec nat 0" while it is expected to have type "vec nat (cast Dyn nat ?u@{n1:=0})". No cast was inserted: the types are not consistent, "0" and "cast Dyn nat ?u@{n1:=0}" differ.
- `vectors.v` v3: return whole (line 24) vec nat 3 -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: The following term contains unresolved implicit arguments: (vhead (cast Dyn (vec nat (S ?n)) v3)) More precisely: - ?n: Cannot infer the implicit parameter n of vhead whose type is "nat".
- `vectors.v` all 13 annotations of the file -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: The following term contains unresolved implicit arguments: (fun (A : Type) (n : nat) (v : Dyn) => cast match ?n with | 0 => unit | S _ => A end Dyn match cast Dyn (vec Dyn ?n) v in vec _ m return match m with | 0 => unit | S _ => A end with | vnil => tt | vcons x _ => cast Dyn A x end) More p
