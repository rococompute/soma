(* Elaboration of gradual CIC: casts are inserted where types are only
   consistent, following GCIC^G *)
From Corelib.Gradual Require Import Gradual.

Definition succ_dyn (x : Any) : nat := x + 1.
Print succ_dyn.

(* a function of unknown type is cast to the germ Any -> Any *)
Definition apply3 (g : Any) : nat := g 3.
Print apply3.

(* Omega, as in the paper *)
Definition delta := fun x : Any => x x.
Print delta.
Definition omega : Any := delta delta.
Print omega.
(* reduction stops after Gradual Steps steps *)
Fail Eval lazy in omega.

(* a type of unknown sort is cast to a universe *)
Definition T (X : Any) : Type := X -> X.
Print T.

(* the expected type list Any reaches both elements *)
Definition mixed : list Any := cons 1 (cons true nil).
Print mixed.

Definition mixed_pair : Any * Any := (1, true).
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
Definition large_list : list Type := @cons Type nat nil.
Definition large_list_dyn : Any := large_list.
Print large_list_dyn.
#[universes(polymorphic)] Record Box@{u} := { contents : Type@{u} }.
Definition box : Box := {| contents := nat |}.
Definition box_dyn : Any := box.
Print box_dyn.
Fail Definition set_dyn : Any := Set.

(* proofs whose evidence is a gradual primitive (unk, raise, a cast to the
   statement), in the proof or in what it uses, are reported; theorems
   about gradual programs, whose casts are their subject, are not *)
Lemma about_program : succ_dyn 41 = 42. Proof. reflexivity. Qed.
Lemma about_program_var : forall n : nat, succ_dyn n = n + 1. Proof. intros n. reflexivity. Qed.
Lemma plain : forall n : nat, 0 + n = n. Proof. reflexivity. Qed.
Lemma by_unknown : False. Proof. exact unk. Qed.
Lemma by_error : forall n : nat, n = 0. Proof. intros; exact raise. Qed.
Lemma by_cast : 0 = 1. Proof. exact (cast (0 = 0) (0 = 1) eq_refl). Qed.
(* a statement about a gradual program does not make unk evidence *)
Lemma about_program_faked : forall n : nat, succ_dyn n = n + 2.
Proof. intros n. exact (eq_trans unk eq_refl). Qed.
(* nor does hiding it in a definition, or in data *)
Definition hidden : 1 = 2 := raise.
Lemma by_hidden : 1 = 2. Proof. exact hidden. Qed.
Definition even_three : {n : nat | Nat.even n = true} := exist _ 3 raise.
Lemma by_data : Nat.even 3 = true. Proof. exact (proj2_sig even_three). Qed.

(* after backtracking, a name may denote a different constant *)
Set Warnings "-undo-batch-mode".
Definition helper : 0 = 0 := eq_refl.
Lemma before_reset : 0 = 0. Proof. exact helper. Qed.
Reset helper.
Definition helper : 0 = 0 := raise.
Lemma after_reset : 0 = 0. Proof. exact helper. Qed.
