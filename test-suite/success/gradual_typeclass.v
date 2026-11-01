(* Type classes under Gradual Typing, and Automatic Generalization *)
From Corelib.Gradual Require Import Gradual.

Class Size (A : Type) := { size : A -> nat }.
#[export] Hint Mode Size + : typeclass_instances.
#[export] Instance size_nat : Size nat := { size n := n }.
#[export] Instance size_bool : Size bool := { size b := if b then 1 else 0 }.

(** The instance binder of [size] occurs nowhere in [A -> nat], but it is
    found by instance resolution, not set to [?]. *)
Definition three := size 3.
Example three_ok : three = 3 := eq_refl.

(** Without the flag, an unknown type is an error. *)
Fail Definition size_plus_one x := size x + 1.

Set Automatic Generalization.

(** An unknown type becomes a maximal implicit type parameter, followed by
    the instances that depend on it. *)
Definition size_plus_one x := size x + 1.
Check @size_plus_one : forall (A : Type) (H : Size A), A -> nat.
Example spo_nat : size_plus_one 4 = 5 := eq_refl.
Example spo_bool : size_plus_one true = 2 := eq_refl.

Definition ident x := x.
Check @ident : forall A : Type, A -> A.

Definition both x y := (size x, size y).
Example both_ok : both 2 false = (2, 0) := eq_refl.

(** A type that is determined is not generalized. *)
Definition plus_one x := x + 1.
Check plus_one : nat -> nat.

(** Any other unsolved evar is still an error. *)
Fail Definition hole : nat := _.

(** A missing instance at a known type is an error, also when evaluating. *)
Fail Definition no_instance := size tt.
Fail Eval lazy in size_plus_one tt.

(** A definitional class, whose instance's type is an arity
    ([Equiv A] is [A -> A -> Prop]): its instance binder occurs nowhere in
    the rest of [equiv]'s type, and it is found by instance resolution all
    the same, not set to [?] (std++ builds its setoids so). *)
Class Equiv A := equiv : A -> A -> Prop.
Class Refl {A} (R : A -> A -> Prop) := refl x : R x x.
Lemma equiv_refl {A} `{Equiv A, !Refl (@equiv A _)} (x : A) : equiv x x.
Proof. apply refl. Qed.
