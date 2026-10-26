(* Gradual CIC, normalization-sacrificing variant (GCIC^G) *)
From Corelib.Gradual Require Import Gradual.

(** * Elaboration: consistent types are accepted and casts are inserted *)

Definition succ_dyn (x : Dyn) : nat := x + 1.
Definition apply3 (g : Dyn) : nat := g 3.

(** The fragment without unknowns is unchanged: inconsistent types are still
    rejected. *)
Fail Definition bad : nat := true.
Fail Check (fun x : nat => x) true.

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

Fail Timeout 1 Eval lazy in omega.
Fail Timeout 1 Eval cbv in omega.
(* Type checking is undecidable: conversion may diverge. *)
Fail Timeout 1 Check (eq_refl : omega = unk).

(** * The gradual axioms are visible *)
Print Assumptions succ_dyn.

(** * Gradual typing can be switched off *)
Unset Gradual Typing.
Fail Definition succ_static (x : Dyn) : nat := x + 1.
