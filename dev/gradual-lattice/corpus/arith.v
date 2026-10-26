(* Arithmetic on nat. *)

Definition double (n : nat) : nat := n + n.

Definition square (n : nat) : nat := n * n.

Fixpoint fact (n : nat) : nat :=
  match n with O => 1 | S k => n * fact k end.

Fixpoint fib (n : nat) : nat :=
  match n with
  | O => 0
  | S k => match k with O => 1 | S j => fib k + fib j end
  end.

Fixpoint pow (b : nat) (e : nat) : nat :=
  match e with O => 1 | S k => b * pow b k end.

Definition is_zero (n : nat) : bool := match n with O => true | S _ => false end.

Definition max3 (a : nat) (b : nat) (c : nat) : nat := Nat.max a (Nat.max b c).

Definition clamp (lo : nat) (hi : nat) (x : nat) : nat :=
  if Nat.leb x lo then lo else if Nat.leb hi x then hi else x.

Definition obs_double : nat := double 21.
Definition obs_square : nat := square 7.
Definition obs_fact : nat := fact 5.
Definition obs_fib : nat := fib 10.
Definition obs_pow : nat := pow 2 6.
Definition obs_is_zero : bool := is_zero 0.
Definition obs_max3 : nat := max3 3 9 4.
Definition obs_clamp : nat := clamp 2 8 11.
