(* Extraction of gradual Rocq: casts are checked at run time.
   Each [t_*] below is also evaluated by the kernel (see the [Goal]s), and
   main.ml checks that the extracted code agrees. *)
From Corelib.Gradual Require Import Gradual.
From Corelib Require Extraction.

Definition succ_dyn (x : Dyn) : nat := x + 1.
Definition apply3 (g : Dyn) : nat := g 3.

(** base types *)
Definition t_ok (_ : unit) := succ_dyn (cast nat Dyn 41).
Definition t_bad (_ : unit) := succ_dyn (cast bool Dyn true).
Goal t_ok tt = 42. Proof. reflexivity. Qed.
Goal t_bad tt = raise. Proof. reflexivity. Qed.

(** functions are wrapped *)
Definition t_app (_ : unit) := apply3 (cast (nat -> nat) Dyn S).
Definition t_app_bad (_ : unit) := apply3 (cast (bool -> bool) Dyn negb).
Goal t_app tt = 4. Proof. reflexivity. Qed.
Goal t_app_bad tt = raise. Proof. reflexivity. Qed.

(** parametrized inductive types: elementwise *)
Definition t_list (_ : unit) : list nat := @cons Dyn 1 (@cons Dyn 2 nil).
Definition t_list_bad (_ : unit) : list nat := @cons Dyn 1 (@cons Dyn true nil).
Goal t_list tt = cons 1 (cons 2 nil). Proof. reflexivity. Qed.
Goal t_list_bad tt = cons 1 (cons raise nil). Proof. reflexivity. Qed.

Definition pr : Dyn * Dyn := @pair Dyn Dyn 1 true.
Definition t_pair (_ : unit) : nat * bool := pr.
Definition t_pair_bad (_ : unit) : bool * nat := pr.

Definition t_option (_ : unit) : option bool := @Some Dyn false.

(** casts of functions inside data are lazy *)
Definition fs : list Dyn := @cons Dyn S (@cons Dyn negb nil).
Definition t_fs (_ : unit) : list (nat -> nat) := fs.

(** records *)
Record point := mkPoint { px : nat; py : bool }.
Definition pt : Dyn := cast point Dyn (mkPoint 1 true).
Definition t_record (_ : unit) : nat := px pt.
Definition t_record_bad (_ : unit) : nat := cast Dyn nat pt.

(** subset types: the proof is erased, the value is cast *)
Definition pos : Dyn := cast {n : nat | 0 < n} Dyn (exist _ 1 (le_n 1)).
Definition t_sig (_ : unit) : nat := proj1_sig (cast Dyn {n : nat | 0 < n} pos).

(** indexed families *)
Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n, A -> vec A n -> vec A (S n).
Arguments vnil {A}. Arguments vcons {A n}.

Definition vhead {A n} (v : vec A (S n)) : A :=
  match v in vec _ m return match m with 0 => unit | S _ => A end with
  | vnil => tt | vcons x _ => x end.

Definition v3 : vec nat unk := vcons 1 (vcons 2 (vcons 3 vnil)).
Definition t_vec (_ : unit) := vhead (v3 : vec nat 3).
Definition t_vec_bad (_ : unit) : vec nat 2 := v3.
Goal vhead (t_vec_bad tt) = raise. Proof. reflexivity. Qed.

(** dependent functions: the codomain depends on the argument *)
Fixpoint rep (n : nat) : vec nat n :=
  match n with 0 => vnil | S k => vcons k (rep k) end.
Definition rep_dyn : Dyn := cast (forall n, vec nat n) Dyn rep.
Definition t_dep (_ : unit) := vhead (cast Dyn (forall n, vec nat n) rep_dyn 3).
Definition t_dep_bad (_ : unit) := vhead (cast Dyn (forall n, vec nat (S n)) rep_dyn 3).
Goal t_dep tt = 2. Proof. reflexivity. Qed.
Goal t_dep_bad tt = raise. Proof. reflexivity. Qed.

(** mutual and nested inductive types *)
Inductive tree (A : Type) := node : A -> forest A -> tree A
with forest (A : Type) := fnil : forest A | fcons : tree A -> forest A -> forest A.
Arguments node {A}. Arguments fnil {A}. Arguments fcons {A}.
Definition tr : tree Dyn := node (cast nat Dyn 1) (fcons (node (cast nat Dyn 2) fnil) fnil).
Definition t_tree (_ : unit) : tree nat := tr.
Definition tr_bad : tree Dyn := node (cast nat Dyn 1) (fcons (node (cast bool Dyn true) fnil) fnil).
Definition t_tree_bad (_ : unit) : tree nat := tr_bad.

#[warnings="-register-all"]
Inductive rose (A : Type) := rnode : A -> list (rose A) -> rose A.
Arguments rnode {A}.
Definition ro : rose Dyn := rnode (cast nat Dyn 1) (cons (rnode (cast nat Dyn 2) nil) nil).
Definition t_rose (_ : unit) : rose nat := ro.

(** the unknown term and the error *)
Definition t_unk (_ : unit) : nat := unk.
Definition t_unk_fun (_ : unit) : nat := (unk : nat -> nat) 3.
Definition t_unk_dyn (_ : unit) : nat := succ_dyn unk.
Definition t_err (_ : unit) : nat := raise.
Definition t_err_fun (_ : unit) : nat -> nat := raise.
Goal t_unk_dyn tt = unk. Proof. reflexivity. Qed.

(** sorts *)
Definition t_sort_bad (_ : unit) : nat := cast Type nat bool.
Goal t_sort_bad tt = raise. Proof. reflexivity. Qed.

(** Omega is well typed, and loops *)
Definition delta := fun x : Dyn => x x.
Definition t_omega (_ : unit) : Dyn := delta (cast (Dyn -> Dyn) Dyn delta).

(** casts at type variables are not supported yet *)
Definition poly (A : Type) (x : A) : Dyn := x.
Fail Extraction poly.

Set Extraction Output Directory ".".
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive unit => "unit" [ "()" ].

Extraction "gradual_prog.ml"
  t_ok t_bad t_app t_app_bad t_list t_list_bad t_pair t_pair_bad t_option
  t_fs t_record t_record_bad t_sig t_vec t_vec_bad t_dep t_dep_bad
  t_tree t_tree_bad t_rose t_unk t_unk_fun t_unk_dyn t_err t_err_fun
  t_sort_bad t_omega vhead.
