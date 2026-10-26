(* Length-indexed vectors. *)

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n, A -> vec A n -> vec A (S n).
Arguments vnil {A}. Arguments vcons {A n}.

Definition vhead {A : Type} {n : nat} (v : vec A (S n)) : A :=
  match v in vec _ m return match m with 0 => unit | S _ => A end with
  | vnil => tt | vcons x _ => x end.

Fixpoint vmap {A B : Type} {n : nat} (f : A -> B) (v : vec A n) : vec B n :=
  match v with vnil => vnil | vcons x r => vcons (f x) (vmap f r) end.

Fixpoint vsum {n : nat} (v : vec nat n) : nat :=
  match v with vnil => 0 | vcons x r => x + vsum r end.

Fixpoint vrep (n : nat) (x : nat) : vec nat n :=
  match n with O => vnil | S k => vcons x (vrep k x) end.

Fixpoint to_list {A : Type} {n : nat} (v : vec A n) : list A :=
  match v with vnil => nil | vcons x r => cons x (to_list r) end.

Definition v3 : vec nat 3 := vcons 1 (vcons 2 (vcons 3 vnil)).

Definition obs_vhead : nat := vhead v3.
Definition obs_vsum : nat := vsum (vmap (fun x : nat => x * 10) v3).
Definition obs_vrep : nat := vsum (vrep 4 5).
Definition obs_to_list : list nat := to_list v3.
