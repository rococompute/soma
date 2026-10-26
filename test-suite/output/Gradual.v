(* Elaboration of gradual CIC: casts are inserted where types are only
   consistent, following GCIC^G *)
From Corelib.Gradual Require Import Gradual.

Definition succ_dyn (x : Dyn) : nat := x + 1.
Print succ_dyn.

(* a function of unknown type is cast to the germ Dyn -> Dyn *)
Definition apply3 (g : Dyn) : nat := g 3.
Print apply3.

(* Omega, as in the paper *)
Definition delta := fun x : Dyn => x x.
Print delta.
Definition omega : Dyn := delta delta.
Print omega.
(* reduction stops after Gradual Steps steps *)
Fail Eval lazy in omega.

(* a type of unknown sort is cast to a universe *)
Definition T (X : Dyn) : Type := X -> X.
Print T.

(* the expected type list Dyn reaches both elements *)
Definition mixed : list Dyn := cons 1 (cons true nil).
Print mixed.

Definition mixed_pair : Dyn * Dyn := (1, true).
Print mixed_pair.

(* the inserted casts compute *)
Eval lazy in succ_dyn 41.
Eval lazy in succ_dyn true.
Eval lazy in apply3 negb.
Eval lazy in (unk : nat -> bool).
Eval lazy in 2 + unk.

(* static errors are still errors *)
Fail Definition bad : nat := true.
(* the error says where the types are not consistent *)
Definition lb : list bool := cons true nil.
Fail Definition bad_list : list nat := lb.
Fail Definition bad_prop : Prop := nat.
Universes i j.
Constraint j < i.
Fail Definition bad_univ (T : Type@{i}) : Type@{j} := T.

(* the universe of gradual types: what can be cast, and what cannot *)
Definition large_list : list Type := cons nat nil.
Definition large_list_dyn : Dyn := large_list.
Print large_list_dyn.
#[universes(polymorphic)] Record Box@{u} := { contents : Type@{u} }.
Definition box : Box := {| contents := nat |}.
Definition box_dyn : Dyn := box.
Print box_dyn.
Fail Definition set_dyn : Dyn := Set.

(* proofs that rely on the gradual primitives in a way their statement
   does not account for are reported; the others are silent *)
Lemma about_program : succ_dyn 41 = 42. Proof. reflexivity. Qed.
Lemma plain : forall n : nat, 0 + n = n. Proof. reflexivity. Qed.
Lemma by_unknown : False. Proof. exact unk. Qed.
Lemma by_error : forall n : nat, n = 0. Proof. intros; exact raise. Qed.
Lemma by_cast : 0 = 1. Proof. exact (cast (0 = 0) (0 = 1) eq_refl). Qed.
