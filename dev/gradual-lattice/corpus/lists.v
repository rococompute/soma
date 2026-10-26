(* Lists of naturals, and polymorphic list functions. *)

Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with nil => nil | cons x r => cons (f x) (map f r) end.

Fixpoint filter {A : Type} (p : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x r => if p x then cons x (filter p r) else filter p r
  end.

Fixpoint fold {A B : Type} (f : A -> B -> B) (l : list A) (z : B) : B :=
  match l with nil => z | cons x r => f x (fold f r z) end.

Fixpoint sum (l : list nat) : nat :=
  match l with nil => 0 | cons x r => x + sum r end.

Fixpoint rev_acc (l : list nat) (acc : list nat) : list nat :=
  match l with nil => acc | cons x r => rev_acc r (cons x acc) end.

Definition rev (l : list nat) : list nat := rev_acc l nil.

Fixpoint mem (x : nat) (l : list nat) : bool :=
  match l with nil => false | cons y r => orb (Nat.eqb x y) (mem x r) end.

Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => cons x nil
  | cons y r => if Nat.leb x y then cons x l else cons y (insert x r)
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with nil => nil | cons x r => insert x (sort r) end.

Fixpoint range (n : nat) : list nat :=
  match n with O => nil | S k => app (range k) (cons k nil) end.

Definition evens (l : list nat) : list nat := filter Nat.even l.

Definition obs_map : list nat := map (fun x : nat => x * 2) (cons 1 (cons 2 (cons 3 nil))).
Definition obs_filter : list nat := evens (range 7).
Definition obs_fold : nat := fold (fun (x : nat) (acc : nat) => x + acc) (range 5) 0.
Definition obs_sum : nat := sum (range 5).
Definition obs_rev : list nat := rev (range 4).
Definition obs_mem : bool := mem 3 (range 5).
Definition obs_sort : list nat := sort (cons 3 (cons 1 (cons 2 nil))).
Definition obs_length : nat := length (range 6).
