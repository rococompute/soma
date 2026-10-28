(* Under Gradual Typing, an application whose expected type does not
   mention [?] is elaborated as in Rocq, arguments first *)
From Corelib.Gradual Require Import Gradual.

Fixpoint P (n : nat) : Prop := match n with 0 => True | S m => P m end.
Lemma P_all : forall n, P n.
Proof. induction n; simpl; auto. Qed.

(* [P_all 3 : P 3], and [P 3] reduces to [True] once [3] is known *)
Goal True. Proof. exact (P_all 3). Qed.

(* lia proves by reflection: its proof term has such a type *)
Require Import Stdlib.micromega.Lia.
Goal forall x y : nat, x < y -> x + 1 <= y. Proof. lia. Qed.
Goal forall p q : nat, q <> 0 -> p * p = 2 * (q * q) -> 0 < p. Proof. nia. Qed.

(* With [?] in the expected type, the expected type still comes first *)
Definition mixed : list Any := cons 1 (cons true nil).
Definition both {A : Type} (x y : A) : A * A := (x, y).
Definition mixed_both : Any * Any := both 1 true.
