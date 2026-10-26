# Graduality lattice

208 mutants of 6 files.

| Static: mutant | count |
|---|---|
| compiled | 193 |
| rejected | 15 |
| out_of_steps | 0 |
| timeout | 0 |

| Dynamic: observation of a compiled mutant | count |
|---|---|
| same | 1320 |
| less_precise | 0 |
| raise | 0 |
| different | 0 |

| Mutants by kind | compiled | rejected | out of steps | timeout |
|---|---|---|---|---|
| single | 155 | 6 | 0 | 0 |
| definition | 34 | 7 | 0 | 0 |
| file | 4 | 2 | 0 | 0 |

| Why mutants are rejected | count |
|---|---|
| type parameter left undetermined by a cast from Dyn | 13 |
| dependent match on a cast to an indexed family (index or return type not inferred) | 2 |

## Mutants that do not compile

- `lists.v` map: all 3 annotations -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: Cannot infer the implicit parameter A of map whose type is "Type" in environment: map : Type -> Type -> Dyn -> Dyn -> Dyn A : Type B : Type f : Dyn l : Dyn x : Dyn r : list Dyn
- `lists.v` filter: all 3 annotations -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: Cannot infer the implicit parameter A of filter whose type is "Type" in environment: filter : Type -> Dyn -> Dyn -> Dyn A : Type p : Dyn l : Dyn x : Dyn r : list Dyn
- `lists.v` fold: all 4 annotations -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: Cannot infer the implicit parameter A of fold whose type is "Type" in environment: fold : Type -> Type -> Dyn -> Dyn -> Dyn -> Dyn A : Type B : Type f : Dyn l : Dyn z : Dyn x : Dyn r : list Dyn
- `lists.v` all 29 annotations of the file -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: Cannot infer the implicit parameter A of map whose type is "Type" in environment: map : Type -> Type -> Dyn -> Dyn -> Dyn A : Type B : Type f : Dyn l : Dyn x : Dyn r : list Dyn
- `vectors.v` vhead: binder whole (line 8) vec A (S n) -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: The following term contains unresolved implicit arguments: (vhead (cast (vec nat 3) Dyn v3)) More precisely: - ?n: Cannot infer the implicit parameter n of vhead whose type is "nat".
- `vectors.v` vhead: all 2 annotations -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: The following term contains unresolved implicit arguments: (cast Dyn nat (vhead (cast (vec nat 3) Dyn v3))) More precisely: - ?A: Cannot infer the implicit parameter A of vhead whose type is "Type". - ?n: Cannot infer the implicit parameter n of vhead whose type is "nat".
- `vectors.v` vmap: binder whole (line 12) vec A n -> Dyn: **rejected** (dependent match on a cast to an indexed family (index or return type not inferred)) — Error: In environment vmap : forall (A B : Type) (n : nat), (A -> B) -> Dyn -> vec B n A : Type B : Type n : nat f : A -> B v : Dyn The term "vnil" has type "vec B 0" while it is expected to have type "vec B n" (cannot unify "0" and "n"). No cast was inserted: the types are not consistent, "0" and "
- `vectors.v` vmap: all 3 annotations -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: Cannot infer the implicit parameter A of vmap whose type is "Type" in environment: vmap : Type -> Type -> nat -> Dyn -> Dyn -> Dyn A : Type B : Type n : nat f : Dyn v : Dyn n0 : nat x : Dyn r : vec Dyn n0
- `vectors.v` vsum: binder whole (line 15) vec nat n -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: Cannot infer the implicit parameter n of vsum whose type is "nat" in environment: vsum : nat -> Dyn -> nat n : nat v : Dyn n0 : nat x : Dyn r : vec Dyn n0
- `vectors.v` vsum: all 2 annotations -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: Cannot infer the implicit parameter n of vsum whose type is "nat" in environment: vsum : nat -> Dyn -> Dyn n : nat v : Dyn n0 : nat x : Dyn r : vec Dyn n0
- `vectors.v` vrep: binder whole (line 18) nat -> Dyn: **rejected** (dependent match on a cast to an indexed family (index or return type not inferred)) — Error: In environment vrep : forall n : Dyn, nat -> vec nat (cast Dyn nat n) n : Dyn x : nat The term "vnil" has type "vec nat 0" while it is expected to have type "vec nat (cast Dyn nat ?u@{n1:=0})". No cast was inserted: the types are not consistent, "0" and "cast Dyn nat ?u@{n1:=0}" differ.
- `vectors.v` to_list: binder whole (line 21) vec A n -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: Cannot infer the implicit parameter n of to_list whose type is "nat" in environment: to_list : forall A : Type, nat -> Dyn -> list A A : Type n : nat v : Dyn n0 : nat x : Dyn r : vec Dyn n0
- `vectors.v` to_list: all 2 annotations -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: Cannot infer the implicit parameter A of to_list whose type is "Type" in environment: to_list : Type -> nat -> Dyn -> Dyn A : Type n : nat v : Dyn n0 : nat x : Dyn r : vec Dyn n0
- `vectors.v` v3: return whole (line 24) vec nat 3 -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: The following term contains unresolved implicit arguments: (vhead (cast Dyn (vec nat (S ?n)) v3)) More precisely: - ?n: Cannot infer the implicit parameter n of vhead whose type is "nat".
- `vectors.v` all 13 annotations of the file -> Dyn: **rejected** (type parameter left undetermined by a cast from Dyn) — Error: Cannot infer the implicit parameter A of vmap whose type is "Type" in environment: vmap : Type -> Type -> nat -> Dyn -> Dyn -> Dyn A : Type B : Type n : nat f : Dyn v : Dyn n0 : nat x : Dyn r : vec Dyn n0
