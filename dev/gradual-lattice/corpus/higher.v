(* Higher-order functions, pairs and options. *)

Definition compose (f : nat -> nat) (g : nat -> nat) (x : nat) : nat := f (g x).

Definition twice (f : nat -> nat) (x : nat) : nat := f (f x).

Fixpoint iter (n : nat) (f : nat -> nat) (x : nat) : nat :=
  match n with O => x | S k => f (iter k f x) end.

Definition swap (p : nat * bool) : bool * nat := (snd p, fst p).

Definition curry (f : nat * nat -> nat) (a : nat) (b : nat) : nat := f (a, b).

Definition uncurry (f : nat -> nat -> nat) (p : nat * nat) : nat := f (fst p) (snd p).

Definition safe_pred (n : nat) : option nat := match n with O => None | S k => Some k end.

Definition with_default (d : nat) (o : option nat) : nat :=
  match o with None => d | Some x => x end.

Definition bind (o : option nat) (f : nat -> option nat) : option nat :=
  match o with None => None | Some x => f x end.

Definition obs_compose : nat := compose (fun x : nat => x + 1) (fun x : nat => x * 3) 4.
Definition obs_twice : nat := twice (fun x : nat => x * x) 3.
Definition obs_iter : nat := iter 4 (fun x : nat => x + 2) 1.
Definition obs_swap : bool * nat := swap (5, true).
Definition obs_curry : nat := curry (fun p : nat * nat => fst p * snd p) 6 7.
Definition obs_uncurry : nat := uncurry Nat.add (20, 22).
Definition obs_bind : nat := with_default 0 (bind (safe_pred 5) safe_pred).
Definition obs_none : nat := with_default 9 (bind (safe_pred 0) safe_pred).
