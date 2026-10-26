(* A small library: finite maps from nat keys, as binary search trees. *)

Inductive tree (V : Type) : Type :=
| Leaf : tree V
| Node : tree V -> nat -> V -> tree V -> tree V.
Arguments Leaf {V}. Arguments Node {V}.

Definition empty {V : Type} : tree V := Leaf.

Fixpoint find {V : Type} (k : nat) (t : tree V) : option V :=
  match t with
  | Leaf => None
  | Node l k' v r =>
    if Nat.ltb k k' then find k l
    else if Nat.ltb k' k then find k r
    else Some v
  end.

Fixpoint add {V : Type} (k : nat) (v : V) (t : tree V) : tree V :=
  match t with
  | Leaf => Node Leaf k v Leaf
  | Node l k' v' r =>
    if Nat.ltb k k' then Node (add k v l) k' v' r
    else if Nat.ltb k' k then Node l k' v' (add k v r)
    else Node l k v r
  end.

Fixpoint remove_min {V : Type} (l : tree V) (k : nat) (v : V) (r : tree V)
  : nat * V * tree V :=
  match l with
  | Leaf => (k, v, r)
  | Node ll lk lv lr =>
    match remove_min ll lk lv lr with (m, mv, l') => (m, mv, Node l' k v r) end
  end.

Definition merge {V : Type} (l : tree V) (r : tree V) : tree V :=
  match r with
  | Leaf => l
  | Node rl rk rv rr =>
    match remove_min rl rk rv rr with (m, mv, r') => Node l m mv r' end
  end.

Fixpoint remove {V : Type} (k : nat) (t : tree V) : tree V :=
  match t with
  | Leaf => Leaf
  | Node l k' v r =>
    if Nat.ltb k k' then Node (remove k l) k' v r
    else if Nat.ltb k' k then Node l k' v (remove k r)
    else merge l r
  end.

Fixpoint fold {V A : Type} (f : nat -> V -> A -> A) (t : tree V) (a : A) : A :=
  match t with
  | Leaf => a
  | Node l k v r => fold f r (f k v (fold f l a))
  end.

Fixpoint elements_acc {V : Type} (t : tree V) (acc : list (nat * V)) : list (nat * V) :=
  match t with
  | Leaf => acc
  | Node l k v r => elements_acc l (cons (k, v) (elements_acc r acc))
  end.

Definition elements {V : Type} (t : tree V) : list (nat * V) := elements_acc t nil.

Definition size {V : Type} (t : tree V) : nat :=
  fold (fun (_ : nat) (_ : V) (n : nat) => S n) t 0.

Fixpoint height {V : Type} (t : tree V) : nat :=
  match t with
  | Leaf => 0
  | Node l _ _ r => S (Nat.max (height l) (height r))
  end.

Fixpoint map_values {V W : Type} (f : V -> W) (t : tree V) : tree W :=
  match t with
  | Leaf => Leaf
  | Node l k v r => Node (map_values f l) k (f v) (map_values f r)
  end.

Fixpoint of_list {V : Type} (l : list (nat * V)) : tree V :=
  match l with
  | nil => Leaf
  | cons (k, v) r => add k v (of_list r)
  end.

Definition find_default {V : Type} (d : V) (k : nat) (t : tree V) : V :=
  match find k t with Some v => v | None => d end.

Definition mem {V : Type} (k : nat) (t : tree V) : bool :=
  match find k t with Some _ => true | None => false end.

Fixpoint counts_acc (l : list nat) (t : tree nat) : tree nat :=
  match l with
  | nil => t
  | cons k r => counts_acc r (add k (S (find_default 0 k t)) t)
  end.

Definition counts (l : list nat) : tree nat := counts_acc l empty.

Definition sample : tree bool :=
  of_list (cons (5, true) (cons (2, false) (cons (8, true) (cons (1, true)
    (cons (9, false) (cons (3, false) nil)))))).

Definition obs_find : option bool := find 8 sample.
Definition obs_find_none : option bool := find 4 sample.
Definition obs_elements : list (nat * bool) := elements sample.
Definition obs_size : nat := size sample.
Definition obs_height : nat := height sample.
Definition obs_remove : list (nat * bool) := elements (remove 5 (remove 2 sample)).
Definition obs_mem : bool := mem 3 (remove 3 sample).
Definition obs_map_values : list (nat * nat) :=
  elements (map_values (fun b : bool => if b then 1 else 0) sample).
Definition obs_counts : list (nat * nat) :=
  elements (counts (cons 3 (cons 1 (cons 3 (cons 2 (cons 3 (cons 1 nil))))))).
