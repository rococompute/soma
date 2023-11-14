Require Import Corelib.Init.Prelude.
Record pair (A : Type) := { first : A; second : A }.
Definition update {A} (p : pair A) (x : A) := {| p with first := x |}.
Check first_set_first.
Check second_set_first.
Goal forall A (p : pair A) x, second A (update p x) = second A p.
Proof. reflexivity. Qed.
Set Universe Polymorphism.
Set Primitive Projections.
Record poly (A : Type) := { left : A; right : A }.
Definition update_poly {A} (p : poly A) (x : A) := {| p with left := x |}.
Check right_set_left.
Goal forall A (p : poly A) x, right A (update_poly p x) = right A p.
Proof. reflexivity. Qed.
(* The update must retain the setter head, rather than expand its body. *)
Goal forall A (p : pair A) (x : A), True.
Proof.
  intros A p x.
  let t := eval unfold update in (@update A p x) in
  lazymatch t with @set_first A x p => exact I end.
Qed.
