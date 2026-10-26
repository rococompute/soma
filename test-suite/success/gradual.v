(* Gradual CIC, normalization-sacrificing variant (GCIC^G) *)
From Corelib.Gradual Require Import Gradual.

(** * Elaboration: consistent types are accepted and casts are inserted *)

Definition succ_dyn (x : Dyn) : nat := x + 1.
Definition apply3 (g : Dyn) : nat := g 3.

(** The fragment without unknowns is unchanged: inconsistent types are still
    rejected. *)
Fail Definition bad : nat := true.
Fail Check (fun x : nat => x) true.

(** * Expected types flow into arguments before they are inferred *)

Definition mixed : list Dyn := cons 1 (cons true nil).
Definition mixed_asc := (cons 1 (cons true nil) : list Dyn).
Definition mixed_pair : Dyn * Dyn := (1, true).

Definition both {A : Type} (x y : A) : A * A := (x, y).
Definition mixed_both : Dyn * Dyn := both 1 true.

Goal (mixed : list nat) = cons 1 (cons raise nil). Proof. reflexivity. Qed.
Goal (mixed : list bool) = cons raise (cons true nil). Proof. reflexivity. Qed.
Goal fst (mixed_pair : nat * nat) = 1. Proof. reflexivity. Qed.
Goal snd (mixed_pair : bool * bool) = true. Proof. reflexivity. Qed.
Goal fst (mixed_both : nat * bool) = 1. Proof. reflexivity. Qed.
Goal snd (mixed_both : nat * bool) = true. Proof. reflexivity. Qed.

(** A precise expected parameter is still a static constraint. *)
Fail Definition still_static : list nat := cons true nil.
Fail Definition still_pair : nat * nat := (true, 1).

(** Explicit type arguments are not overridden by the expected type: a
    less precise one is cast, as the precise one is accepted (graduality). *)
Definition some_precise : option bool := @Some bool false.
Definition some_dyn : option bool := @Some Dyn false.
Definition cons_dyn : list nat := @cons Dyn 1 (@cons Dyn 2 nil).
Definition cons_dyn_bad : list nat := @cons Dyn 1 (@cons Dyn true nil).
Definition pair_dyn : nat * bool := @pair Dyn Dyn 1 true.
Goal some_dyn = Some false. Proof. reflexivity. Qed.
Goal cons_dyn = cons 1 (cons 2 nil). Proof. reflexivity. Qed.
Goal cons_dyn_bad = cons 1 (cons raise nil). Proof. reflexivity. Qed.
Goal pair_dyn = (1, true). Proof. reflexivity. Qed.
Fail Definition some_wrong : option bool := @Some nat 0.

(** At [Dyn], parameters left undetermined are [Dyn]; explicit ones win. *)
Definition mixed_dyn : Dyn := cons 1 (cons true nil).
Definition mixed_pair_dyn : Dyn := (1, true).
Definition explicit_dyn : Dyn := @cons nat 1 nil.
Fail Definition explicit_bad : Dyn := @cons nat 1 (cons true nil).
Goal (mixed_dyn : list nat) = cons 1 (cons raise nil). Proof. reflexivity. Qed.
Goal (explicit_dyn : list nat) = cons 1 nil. Proof. reflexivity. Qed.

(** * Casts from [Dyn] do not leave arguments undetermined *)

(* the other component of a pair, the length of a vector: [?] *)
Definition snd_dyn (p : Dyn) : bool := snd p.
Goal snd_dyn (cast (nat * bool) Dyn (1, true)) = true. Proof. reflexivity. Qed.
Definition if_dyn (b : Dyn) : nat := if b then 1 else 0.
Goal if_dyn (cast bool Dyn false) = 0. Proof. reflexivity. Qed.
Goal if_dyn (cast nat Dyn 3) = raise. Proof. reflexivity. Qed.

(** * Recursion through [Dyn]

    GCIC^G gives up termination: a fixpoint that recurses through [Dyn] has
    no structural guard, and is accepted without checking one (with a
    warning). It unfolds on the values of [Dyn], and these unfoldings count
    towards Gradual Steps. *)
#[warnings="-gradual-unguarded-fixpoint"]
Fixpoint fact_dyn (n : Dyn) : nat := match n with O => 1 | S k => n * fact_dyn k end.
Goal fact_dyn 5 = 120. Proof. reflexivity. Qed.
Goal fact_dyn true = raise. Proof. reflexivity. Qed.
Goal True.
  assert (fact_dyn 4 = 24) by (cbv; reflexivity).
  assert (fact_dyn 4 = 24) by (cbn; reflexivity).
  assert (fact_dyn 4 = 24) by (simpl; reflexivity).
  exact I.
Qed.
(* a constructor argument made [Dyn]: [eval a] is not structural *)
Inductive dexpr := DNum (n : nat) | DPlus (a : Dyn) (b : dexpr).
#[warnings="-gradual-unguarded-fixpoint"]
Fixpoint deval (e : dexpr) : nat := match e with DNum n => n | DPlus a b => deval a + deval b end.
Goal deval (DPlus (DPlus (DNum 1) (DNum 2)) (DNum 3)) = 6. Proof. reflexivity. Qed.
(* a loop through [Dyn] stops at the step budget *)
#[warnings="-gradual-unguarded-fixpoint"]
Fixpoint loop_dyn (n : Dyn) : nat := loop_dyn n.
Fail Eval lazy in loop_dyn 0.
(* without gradual primitives, the guard is still checked *)
Fail Fixpoint not_structural (n : nat) : nat := not_structural n.

(** * Implicit arguments that precision erased

    An implicit argument whose binder occurs nowhere in the rest of the type
    of the function can never be determined: it is [?]. *)
#[warnings="-gradual-unguarded-fixpoint"]
Fixpoint map_dyn {A B : Type} (f : Dyn) (l : Dyn) : Dyn :=
  match l with nil => nil | cons x r => cons (f x) (map_dyn f r) end.
Definition map_obs : list nat := map_dyn (fun x : nat => x * 2) (cons 1 (cons 2 (cons 3 nil))).
Goal map_obs = cons 2 (cons 4 (cons 6 nil)). Proof. reflexivity. Qed.
(* [A] occurs in [list A]: still an error *)
Fail Definition no_type := nil.

(** In a [match] with a return clause, the indices of a cast from [Dyn] are
    not [?]: the return type may depend on them. *)
Module DependentMatch.
  Inductive vec (A : Type) : nat -> Type :=
  | vnil : vec A 0
  | vcons : forall n, A -> vec A n -> vec A (S n).
  Arguments vnil {A}. Arguments vcons {A n}.
  Fail Definition vhead_dyn {A : Type} (v : Dyn) : A :=
    match v in vec _ m return match m with 0 => unit | S _ => A end with
    | vnil => tt | vcons x _ => x end.
  (* without a return clause, they are *)
  #[warnings="-gradual-unguarded-fixpoint"]
  Fixpoint vsum_dyn (v : Dyn) : nat :=
    match v with vnil => 0 | vcons x r => x + vsum_dyn r end.
  Goal vsum_dyn (cast (vec nat 2) Dyn (vcons 1 (vcons 2 vnil))) = 3. Proof. reflexivity. Qed.
End DependentMatch.

(** * Graduality: a term accepted at a type is accepted at less precise ones

    Each group gives one term at decreasingly precise types. *)
Module Graduality.
  Definition l_nat : list nat := cons 1 (cons 2 nil).
  Definition l_list : list Dyn := cons 1 (cons 2 nil).
  Definition l_dyn : Dyn := cons 1 (cons 2 nil).

  Definition c_nat : list nat := @cons nat 1 nil.
  Definition c_dyn : list nat := @cons Dyn 1 nil.

  Definition s_bool : option bool := @Some bool false.
  Definition s_dyn : option bool := @Some Dyn false.

  (* the given argument wins over what the expected type fixes for it *)
  Definition e_nat := @eq_refl _ 0 : 0 = 0.
  Definition e_dyn := @eq_refl _ unk : 0 = unk.

  Definition m_list : list Dyn := cons 1 (cons true nil).
  Definition m_dyn : Dyn := cons 1 (cons true nil).

  Definition b_nat : nat * nat := both 1 1.
  Definition b_pair : Dyn * Dyn := both 1 1.
  Definition b_dyn : Dyn := both 1 1.

  (* annotated binders: the annotation is consistent with the domain *)
  Definition f_nat : nat -> nat := fun x : nat => x.
  Definition f_dom : Dyn -> nat := fun x : nat => x.
  Definition f_fun : Dyn -> Dyn := fun x : nat => x.
  Definition f_dyn : Dyn := fun x : nat => x.
  Goal f_dom (cast nat Dyn 3) = 3. Proof. reflexivity. Qed.
  Goal f_dom (cast bool Dyn true) = raise. Proof. reflexivity. Qed.

  (* still static errors: inconsistent annotations *)
  Fail Definition f_bad : nat -> nat := fun x : bool => x.
  Fail Definition f_bad' : bool -> nat := fun x : nat => x.
End Graduality.

(** * Reduction of casts *)

Goal succ_dyn 41 = 42. Proof. reflexivity. Qed.
Goal succ_dyn true = raise. Proof. reflexivity. Qed.
Goal apply3 S = 4. Proof. reflexivity. Qed.
Goal apply3 negb = raise. Proof. reflexivity. Qed.

(** round trips through the unknown type *)
Goal cast Dyn nat (cast nat Dyn 3) = 3. Proof. reflexivity. Qed.
Goal cast Dyn bool (cast nat Dyn 3) = raise. Proof. reflexivity. Qed.
Goal cast Dyn Dyn (cast nat Dyn 3) = cast nat Dyn 3. Proof. reflexivity. Qed.

(** parametrized inductive types *)
Definition l : list Dyn := @cons Dyn 1 (@cons Dyn true nil).
Goal (l : list nat) = cons 1 (cons raise nil). Proof. reflexivity. Qed.

(** functions between Pi types are wrapped lazily *)
Goal (cast (nat -> nat) (bool -> bool) S) = fun b => cast nat bool (S (cast bool nat b)).
Proof. reflexivity. Qed.

(** head mismatches raise *)
Goal cast Type nat bool = raise. Proof. reflexivity. Qed.
Goal cast (nat -> nat) nat S = raise. Proof. reflexivity. Qed.

(** * Conversion under binders

    The kernel compares these types under the binder without adding it to
    the environment: the rules must keep its variable apart from the
    variables of the environment. *)
Definition under_binder : forall m : nat, cast nat nat m = m := fun m => eq_refl.
Definition under_binder_dyn : forall m : nat, cast Dyn nat (cast nat Dyn m) = m :=
  fun m => eq_refl.
Definition under_binder_list :
  forall m : nat, cast (list Dyn) (list nat) (cons (cast nat Dyn m) nil) = cons m nil :=
  fun m => eq_refl.
Lemma under_binder_fun : forall (f : nat -> nat) (n : nat),
  cast (Dyn -> Dyn) (nat -> nat) (cast (nat -> nat) (Dyn -> Dyn) f) n = f n.
Proof. intros. reflexivity. Qed.

(** * Primitive types *)

Module Prim.
  From Corelib Require Import PrimInt63 PrimFloat PrimString PrimArray.
  Goal cast Dyn int (cast int Dyn 3%uint63) = 3%uint63. Proof. reflexivity. Qed.
  Goal cast int nat 3%uint63 = raise. Proof. reflexivity. Qed.
  Goal cast float int 1.5%float = raise. Proof. reflexivity. Qed.
  Goal cast string int "a"%pstring = raise. Proof. reflexivity. Qed.
  Goal cast int Type 3%uint63 = raise. Proof. reflexivity. Qed.
  (* the elements of arrays are not cast: such a cast is stuck *)
  Goal True.
    let t := eval lazy in (cast (array nat) (array bool) (make 1 0)) in
    match t with cast _ _ _ => idtac end.
    exact I.
  Qed.
End Prim.

(** * Sorts: consistent only when cumulative *)

(** Without [?], elaboration is CIC: a type is not cast into [Prop] or into
    a lower universe. *)
Fail Definition bad_prop : Prop := nat.
Universes i j.
Constraint j < i.
Constraint i < Corelib.Gradual.Gradual.gradual.
Fail Definition down (T : Type@{i}) : Type@{j} := T.
Definition up (T : Type@{j}) : Type@{i} := T.

(** Codomains are cumulative, as in Rocq. *)
Definition const_nat (_ : Dyn) : Set := nat.
Definition cumul_codomain : nat -> Type := const_nat.
Fail Definition bad_codomain : nat -> Set := (fun _ : nat => nat : Type).

(** Casts between sorts follow the universe graph. *)
Goal cast Type@{j} Type@{i} nat = nat. Proof. reflexivity. Qed.
Goal cast Type@{i} Type@{j} nat = raise. Proof. reflexivity. Qed.
Goal cast Prop Set True = True. Proof. reflexivity. Qed.
Goal cast Set Prop nat = raise. Proof. reflexivity. Qed.

(** * The unknown and error terms *)

Goal (unk : nat -> bool) = fun _ => unk. Proof. reflexivity. Qed.
Goal match (unk : nat) with 0 => true | S _ => false end = unk. Proof. reflexivity. Qed.
Goal match (raise : nat) with 0 => true | S _ => false end = raise. Proof. reflexivity. Qed.
Goal 2 + unk = S (S unk). Proof. reflexivity. Qed.
Goal unk + 2 = unk. Proof. reflexivity. Qed.

(** dependent elimination: the return type is instantiated with ?_I *)
Goal match (unk : nat) as n return (match n with 0 => bool | S _ => nat end) with
     | 0 => true | S k => k end = unk.
Proof. reflexivity. Qed.

(** primitive projections *)
Module Proj.
  Set Primitive Projections.
  Record point := mkPoint { px : nat; py : bool }.
  Goal (unk : point).(px) = unk. Proof. reflexivity. Qed.
  Goal (raise : point).(py) = raise. Proof. reflexivity. Qed.
End Proj.

(** * Indexed families (extension: the GCIC paper only has parameters) *)

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n, A -> vec A n -> vec A (S n).
Arguments vnil {A}. Arguments vcons {A n}.

Definition vhead {A n} (v : vec A (S n)) : A :=
  match v in vec _ m return match m with 0 => unit | S _ => A end with
  | vnil => tt | vcons x _ => x end.

Definition v3 : vec nat unk := vcons 1 (vcons 2 (vcons 3 vnil)).
Goal vhead (v3 : vec nat 3) = 1. Proof. reflexivity. Qed.
Goal (v3 : vec nat 2) = raise. Proof. reflexivity. Qed.

(** * All reduction strategies implement the rules *)

Goal True.
Proof.
  assert (H : succ_dyn true = raise) by (lazy; reflexivity).
  assert (H1 : succ_dyn 41 = 42) by (cbv; reflexivity).
  assert (H2 : succ_dyn 41 = 42) by (cbn; reflexivity).
  assert (H3 : succ_dyn 41 = 42) by (vm_compute; reflexivity).
  assert (H4 : unk + 2 = unk) by (simpl; reflexivity).
  exact I.
Qed.

(** * Normalization is lost: Omega is well typed *)

Definition delta := fun x : Dyn => x x.
Definition omega : Dyn := delta delta.

(* Reduction and conversion stop with an error after [Gradual Steps]
   gradual steps (100000 by default) instead of hanging. *)
Fail Eval lazy in omega.
Fail Eval cbv in omega.
Fail Eval cbn in omega.
(* Type checking is undecidable: conversion may diverge. *)
Fail Check (eq_refl : omega = unk).
Goal omega = unk. Proof. Fail reflexivity. Abort.

(* The budget counts gradual steps only, and each command has its own: these
   come right after commands that spent theirs. *)
Goal 1 + 1 = 2. Proof. reflexivity. Qed.
Goal succ_dyn 41 = 42. Proof. reflexivity. Qed.
Set Gradual Steps 1.
Fail Eval lazy in succ_dyn 41.
Set Gradual Steps 100000.
Eval lazy in succ_dyn 41.

(* Without a limit, Omega loops. *)
Unset Gradual Steps.
Fail Timeout 1 Eval lazy in omega.
Set Gradual Steps 100000.

(** * The gradual axioms are visible *)
Print Assumptions succ_dyn.

(** * Gradual typing can be switched off *)
Unset Gradual Typing.
Fail Definition succ_static (x : Dyn) : nat := x + 1.
