(* Extraction of gradual Rocq: casts are checked at run time.
   Each [t_*] below has a [Goal] giving its value, which every reduction
   machine must compute ([machines]); main.ml checks that the extracted code
   agrees, up to the differences documented in GRADUAL.md. *)
From Corelib.Gradual Require Import Gradual.
From Corelib Require Extraction.
From Corelib Require Import PrimInt63 PrimFloat.
From Corelib Require PrimArray.

(* Both sides have the same normal form, up to universes and not only up
   to conversion, under each reduction machine: lazy (the kernel machine),
   cbv, cbn and simpl (after unfolding definitions, which they fold back
   otherwise), and vm_compute (which falls back to cbv under Gradual
   Typing). *)
Ltac machines :=
  match goal with |- ?a = ?b =>
    let a1 := eval lazy in a in let b1 := eval lazy in b in constr_eq_nounivs a1 b1;
    let a2 := eval cbv in a in let b2 := eval cbv in b in constr_eq_nounivs a2 b2;
    let a3 := eval cbv delta in a in let a3 := eval cbn in a3 in
    let b3 := eval cbv delta in b in let b3 := eval cbn in b3 in constr_eq_nounivs a3 b3;
    let a4 := eval cbv delta in a in let a4 := eval simpl in a4 in
    let b4 := eval cbv delta in b in let b4 := eval simpl in b4 in constr_eq_nounivs a4 b4;
    let a5 := eval vm_compute in a in let b5 := eval vm_compute in b in constr_eq_nounivs a5 b5;
    reflexivity
  end.

Definition succ_dyn (x : Any) : nat := x + 1.
Definition apply3 (g : Any) : nat := g 3.

(** base types *)
Definition t_ok (_ : unit) := succ_dyn (cast nat Any 41).
Definition t_bad (_ : unit) := succ_dyn (cast bool Any true).
Goal t_ok tt = 42. Proof. machines. Qed.
Goal t_bad tt = raise. Proof. machines. Qed.

(** functions are wrapped *)
Definition t_app (_ : unit) := apply3 (cast (nat -> nat) Any S).
Definition t_app_bad (_ : unit) := apply3 (cast (bool -> bool) Any negb).
Goal t_app tt = 4. Proof. machines. Qed.
Goal t_app_bad tt = raise. Proof. machines. Qed.

(** parametrized inductive types: elementwise *)
Definition t_list (_ : unit) : list nat := @cons Any 1 (@cons Any 2 nil).
Definition t_list_bad (_ : unit) : list nat := @cons Any 1 (@cons Any true nil).
Goal t_list tt = cons 1 (cons 2 nil). Proof. machines. Qed.
(* only the elements that are used are eliminated *)
Definition t_list_bad_length (_ : unit) := length (t_list_bad tt).
Definition t_list_bad_head (_ : unit) := match t_list_bad tt with cons x _ => x | nil => 0 end.
Goal t_list_bad_length tt = 2. Proof. machines. Qed.
Goal t_list_bad_head tt = 1. Proof. machines. Qed.
Goal t_list_bad tt = cons 1 (cons raise nil). Proof. machines. Qed.

Definition pr : Any * Any := @pair Any Any 1 true.
Definition t_pair (_ : unit) : nat * bool := pr.
Definition t_pair_bad (_ : unit) : bool * nat := pr.
Goal t_pair tt = (1, true). Proof. machines. Qed.
Goal t_pair_bad tt = (raise, raise). Proof. machines. Qed.

Definition t_option (_ : unit) : option bool := @Some Any false.
Goal t_option tt = Some false. Proof. machines. Qed.

(** casts of functions inside data are lazy *)
Definition fs : list Any := @cons Any S (@cons Any negb nil).
Definition t_fs (_ : unit) : list (nat -> nat) := fs.
Goal match t_fs tt with cons f (cons g nil) => (f 1, g 1) | _ => (0, 0) end = (2, raise).
Proof. machines. Qed.

(** records *)
Record point := mkPoint { px : nat; py : bool }.
Definition pt : Any := cast point Any (mkPoint 1 true).
Definition t_record (_ : unit) : nat := px pt.
Definition t_record_bad (_ : unit) : nat := cast Any nat pt.
Goal t_record tt = 1. Proof. machines. Qed.
Goal t_record_bad tt = raise. Proof. machines. Qed.

(** subset types: the proof is erased, the value is cast *)
Definition pos : Any := cast {n : nat | 0 < n} Any (exist _ 1 (le_n 1)).
Definition t_sig (_ : unit) : nat := proj1_sig (cast Any {n : nat | 0 < n} pos).
Goal t_sig tt = 1. Proof. machines. Qed.

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
Goal vhead (t_vec_bad tt) = raise. Proof. machines. Qed.
Goal t_vec tt = 1. Proof. machines. Qed.
Goal t_vec_bad tt = raise. Proof. machines. Qed.

(** dependent functions: the codomain depends on the argument *)
Fixpoint rep (n : nat) : vec nat n :=
  match n with 0 => vnil | S k => vcons k (rep k) end.
Definition rep_dyn : Any := cast (forall n, vec nat n) Any rep.
Definition t_dep (_ : unit) := vhead (cast Any (forall n, vec nat n) rep_dyn 3).
Definition t_dep_bad (_ : unit) := vhead (cast Any (forall n, vec nat (S n)) rep_dyn 3).
Goal t_dep tt = 2. Proof. machines. Qed.
Goal t_dep_bad tt = raise. Proof. machines. Qed.

(** mutual and nested inductive types *)
Inductive tree (A : Type) := node : A -> forest A -> tree A
with forest (A : Type) := fnil : forest A | fcons : tree A -> forest A -> forest A.
Arguments node {A}. Arguments fnil {A}. Arguments fcons {A}.
Definition tr : tree Any := node (cast nat Any 1) (fcons (node (cast nat Any 2) fnil) fnil).
Definition t_tree (_ : unit) : tree nat := tr.
Definition tr_bad : tree Any := node (cast nat Any 1) (fcons (node (cast bool Any true) fnil) fnil).
Definition t_tree_bad (_ : unit) : tree nat := tr_bad.
Definition t_tree_bad_root (_ : unit) := match t_tree_bad tt with node x _ => x end.
Goal t_tree_bad_root tt = 1. Proof. machines. Qed.
Goal t_tree tt = node 1 (fcons (node 2 fnil) fnil). Proof. machines. Qed.
Goal t_tree_bad tt = node 1 (fcons (node raise fnil) fnil). Proof. machines. Qed.

#[warnings="-register-all"]
Inductive rose (A : Type) := rnode : A -> list (rose A) -> rose A.
Arguments rnode {A}.
Definition ro : rose Any := rnode (cast nat Any 1) (cons (rnode (cast nat Any 2) nil) nil).
Definition t_rose (_ : unit) : rose nat := ro.
Goal t_rose tt = rnode 1 (cons (rnode 2 nil) nil). Proof. machines. Qed.

(** the unknown term and the error *)
Definition t_unk (_ : unit) : nat := unk.
Definition t_unk_fun (_ : unit) : nat := (unk : nat -> nat) 3.
Definition t_unk_dyn (_ : unit) : nat := succ_dyn unk.
Definition t_unk_plus (_ : unit) : nat := 2 + unk.
Definition t_unk_elim (_ : unit) : nat := unk + 2.
Goal t_unk_plus tt = S (S unk). Proof. machines. Qed.
Goal t_unk_elim tt = unk. Proof. machines. Qed.
(* a match on [unk] is [unk] at its type, here the mapped bool *)
Definition t_elim_mapped (_ : unit) : bool := match (unk : nat) with O => true | S _ => false end.
Goal t_elim_mapped tt = unk. Proof. machines. Qed.
Definition t_err (_ : unit) : nat := raise.
Definition t_err_fun (_ : unit) : nat -> nat := raise.
Goal t_unk_dyn tt = unk. Proof. machines. Qed.
Goal t_unk tt = unk. Proof. machines. Qed.
Goal t_unk_fun tt = unk. Proof. machines. Qed.
Goal t_err tt = raise. Proof. machines. Qed.
Goal t_err_fun tt = raise. Proof. machines. Qed.

(** sorts *)
Definition t_sort_bad (_ : unit) : nat := cast Type nat bool.
Goal t_sort_bad tt = raise. Proof. machines. Qed.

(** primitive types: equal ones cast to themselves, others clash *)
Definition t_int (_ : unit) : int := cast Any int (cast int Any 3%uint63).
Definition t_int_bad (_ : unit) : nat := cast Any nat (cast int Any 3%uint63).
Definition t_int_float (_ : unit) : float := cast Any float (cast int Any 3%uint63).
Goal t_int tt = 3%uint63. Proof. machines. Qed.
Goal t_int_bad tt = raise. Proof. machines. Qed.
Goal t_int_float tt = raise. Proof. machines. Qed.
(* casts do not visit the elements of arrays: the kernel leaves a cast
   between array types with different elements stuck *)
Definition t_array (_ : unit) : PrimArray.array bool :=
  cast Any (PrimArray.array bool) (cast (PrimArray.array nat) Any (PrimArray.make 1%uint63 0)).
Goal True.
Proof.
  let t := eval lazy in (t_array tt) in match t with cast _ _ _ => idtac end.
  exact I.
Qed.

(** Omega is well typed, and loops *)
Definition delta := fun x : Any => x x.
Definition t_omega (_ : unit) : Any := delta (cast (Any -> Any) Any delta).

(** type parameters: the ones casts need are passed at run time *)
Definition to_dyn {A : Type} (x : A) : Any := x.
Definition of_dyn {A : Type} (d : Any) : A := d.
Definition roundtrip {A B : Type} (x : A) : B := of_dyn (to_dyn x).
Fixpoint dyns {A : Type} (l : list A) : list Any :=
  match l with nil => nil | cons x r => cons (to_dyn x) (dyns r) end.
Definition dyns_local {A : Type} (l : list A) : list Any :=
  (fix go (l : list A) := match l with nil => nil | cons x r => cons (x : Any) (go r) end) l.
Fixpoint ev {A : Type} (l : list A) : list Any :=
  match l with nil => nil | cons x r => cons (to_dyn x) (od r) end
with od {A : Type} (l : list A) : list Any :=
  match l with nil => nil | cons x r => cons (x : Any) (ev r) end.
Definition poly_fun {A : Type} (f : A -> A) : Any := f.

Definition t_poly (_ : unit) : nat := roundtrip 41.
Definition t_poly_bad (_ : unit) : bool := roundtrip 41.
Definition t_poly_list (_ : unit) : list nat := of_dyn (to_dyn (dyns (cons 1 (cons 2 nil)))).
Definition t_poly_rec (_ : unit) : list nat := dyns (cons 1 (cons 2 nil)).
Definition t_poly_rec_bad (_ : unit) : list bool := dyns (cons 1 (cons 2 nil)).
Definition t_poly_local (_ : unit) : list bool := dyns_local (cons true nil).
Definition t_poly_mutual (_ : unit) : list nat := ev (cons 1 (cons 2 (cons 3 nil))).
Definition t_poly_fun (_ : unit) : nat := (of_dyn (poly_fun S) : nat -> nat) 1.
Definition t_poly_fun_bad (_ : unit) : nat := (of_dyn (poly_fun negb) : nat -> nat) 1.
Goal t_poly tt = 41. Proof. machines. Qed.
Goal t_poly_bad tt = raise. Proof. machines. Qed.
Goal t_poly_list tt = cons 1 (cons 2 nil). Proof. machines. Qed.
Goal t_poly_rec tt = cons 1 (cons 2 nil). Proof. machines. Qed.
Goal t_poly_local tt = cons true nil. Proof. machines. Qed.
Goal t_poly_fun_bad tt = raise. Proof. machines. Qed.
Goal t_poly_rec_bad tt = cons raise (cons raise nil). Proof. machines. Qed.
Goal t_poly_mutual tt = cons 1 (cons 2 (cons 3 nil)). Proof. machines. Qed.
Goal t_poly_fun tt = 2. Proof. machines. Qed.

(** not supported: a function needing type parameters at run time used
    without them, and type abstractions that are not parameters of a
    constant *)
Definition apply_poly (f : forall A : Type, A -> Any) := f nat 3.
Definition bad_first_class := apply_poly (@to_dyn).
Fail Extraction bad_first_class.
Definition bad_local := let g (A : Type) (x : A) : Any := x in g nat 1.
Fail Extraction bad_local.

Set Extraction Output Directory ".".
(* nat, list, prod and option are extracted as OCaml variants, which can
   hold [?] and [err] as values; bool is mapped to OCaml's bool, which
   cannot, so casts to bool raise at once. *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive unit => "unit" [ "()" ].
(* primitive integers, as OCaml integers (see uint63.ml) *)
Extract Inlined Constant int => "Uint63.t".
Extract Inlined Constant float => "float".
Extract Constant PrimArray.array "'a" => "'a Stdlib.Array.t".
Extract Inlined Constant PrimArray.make => "Array.make".

Extraction "gradual_prog.ml"
  t_ok t_bad t_app t_app_bad t_list t_list_bad t_list_bad_length t_list_bad_head
  t_pair t_pair_bad t_option t_tree_bad_root t_unk_plus t_unk_elim t_elim_mapped
  t_int t_int_bad t_int_float t_array
  t_fs t_record t_record_bad t_sig t_vec t_vec_bad t_dep t_dep_bad
  t_tree t_tree_bad t_rose t_unk t_unk_fun t_unk_dyn t_err t_err_fun
  t_sort_bad t_omega vhead
  t_poly t_poly_bad t_poly_list t_poly_rec t_poly_rec_bad t_poly_local
  t_poly_mutual t_poly_fun t_poly_fun_bad.
