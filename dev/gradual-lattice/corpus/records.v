(* A record, and functions on it. *)

Record point := mk_point { px : nat; py : nat }.

Definition origin : point := mk_point 0 0.

Definition shift (dx : nat) (p : point) : point := mk_point (px p + dx) (py p).

Definition manhattan (p : point) : nat := px p + py p.

Definition same_x (p : point) (q : point) : bool := Nat.eqb (px p) (px q).

Definition diag (n : nat) : point := mk_point n n.

Definition obs_shift : nat := manhattan (shift 3 (diag 2)).
Definition obs_same : bool := same_x (shift 0 origin) origin.
Definition obs_px : nat := px (shift 5 origin).
