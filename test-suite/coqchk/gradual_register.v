(* The gradual primitives registered in this very file: rocqchk must
   install their reduction rules before checking the lemmas below, which
   only hold by computation. *)
Universe gradual.
Axiom unknown : forall A : Type@{gradual}, A.
Axiom err : forall A : Type@{gradual}, A.
Axiom cast : forall A B : Type@{gradual}, A -> B.
Register unknown as kernel.gradual_unknown.
Register err as kernel.gradual_err.
Register cast as kernel.gradual_cast.

Inductive nat := O | S (n : nat).
Inductive bool := true | false.
Inductive eq {A : Type} (x : A) : A -> Prop := eq_refl : eq x x.

Definition Any := unknown Type.
Definition roundtrip : eq (cast Any nat (cast nat Any (S O))) (S O) := eq_refl _.
Definition mismatch : eq (cast Any bool (cast nat Any O)) (err bool) := eq_refl _.
