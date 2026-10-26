(* Gradual casts at indexed families (beyond the GCIC paper, which only has
   parameters): the indices a rebuilt constructor computes must be
   compatible with the target ones, and a cast whose indices cannot be
   decided (neutral terms) stays stuck, instead of raising or looping.
   See [check_index] in kernel/gradual.ml. *)
From Corelib.Gradual Require Import Gradual.

(* [t] reduces (lazy) to a cast that does not compute further. *)
Ltac stuck t :=
  let t := eval lazy in t in
  match t with
  | cast _ _ _ => idtac
  | _ => fail "not stuck:" t
  end.

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n, A -> vec A n -> vec A (S n).
Arguments vnil {A}. Arguments vcons {A n}.

Definition vhead {A n} (v : vec A (S n)) : A :=
  match v in vec _ m return match m with 0 => unit | S _ => A end with
  | vnil => tt | vcons x _ => x end.
Definition vtail {A n} (v : vec A (S n)) : vec A n :=
  match v in vec _ m return match m with 0 => unit | S k => vec A k end with
  | vnil => tt | vcons _ t => t end.

(** * Unknown length, heterogeneous elements *)

(* The expected type gives the parameter: [vcons] is checked at [Dyn], and
   the unknown length is a cast from [vec Dyn 2]. *)
Definition v2 : vec Dyn unk := vcons 1 (vcons true vnil).

Definition v2_ok : vec Dyn 2 := v2.
Definition v2_short : vec Dyn 1 := v2.
Goal v2_ok = vcons (cast nat Dyn 1) (vcons (cast bool Dyn true) vnil). Proof. reflexivity. Qed.
Goal v2_short = raise. Proof. reflexivity. Qed.
Goal (vhead v2_ok : nat) = 1. Proof. reflexivity. Qed.
Goal (vhead (vtail v2_ok) : nat) = raise. Proof. reflexivity. Qed.

(** * Neutral indices: the cast is stuck *)

Section Neutral.
  Variable n : nat.
  Variable v : vec nat n.

  Goal cast (vec nat n) (vec nat n) v = v. Proof. reflexivity. Qed.
  (* [v] is not a constructor *)
  Goal True. stuck (cast (vec nat n) (vec nat (S n)) v). exact I. Qed.
  (* the computed index [S n] is the target one *)
  Goal cast (vec nat unk) (vec nat (S n)) (vcons 0 v) = vcons 0 v. Proof. reflexivity. Qed.
  (* [S n] against [S (S n)]: [n] against [S n] is not decided *)
  Goal True. stuck (cast (vec nat unk) (vec nat (S (S n))) (vcons 0 v)). exact I. Qed.
  (* distinct constructors: a mismatch *)
  Goal cast (vec nat unk) (vec nat 0) (vcons 0 v) = raise. Proof. reflexivity. Qed.
End Neutral.

(** * Equality *)

Section Eq.
  Variable n m : nat.
  Variable e : n = m.
  Goal True. stuck (cast (n = m) (n = n) e). exact I. Qed.
  Goal cast (n = n) (n = unk) (eq_refl n) = eq_refl n. Proof. reflexivity. Qed.
  Goal cast (0 = 0) (0 = 1) (eq_refl 0) = raise. Proof. reflexivity. Qed.
End Eq.

(** * Fin *)

Inductive Fin : nat -> Type :=
| F1 : forall n, Fin (S n)
| FS : forall n, Fin n -> Fin (S n).

Goal cast (Fin unk) (Fin 2) (FS 1 (F1 0)) = FS 1 (F1 0). Proof. reflexivity. Qed.
Goal cast (Fin unk) (Fin 3) (FS 1 (F1 0)) = raise. Proof. reflexivity. Qed.
Goal cast (Fin unk) (Fin 1) (FS 1 (F1 0)) = raise. Proof. reflexivity. Qed.
Section FinN.
  Variable n : nat.
  Goal cast (Fin unk) (Fin (S n)) (F1 n) = F1 n. Proof. reflexivity. Qed.
  (* [S n] against [n] *)
  Goal True. stuck (cast (Fin unk) (Fin n) (F1 n)). exact I. Qed.
End FinN.

(** * Matching on [?] and [err] at an indexed type *)

(* the return type mentions the index: [match ?_(vec A n) return P] is
   [?_(P n ?)] *)
Definition dep {A n} (v : vec A n) : match n with 0 => unit | S _ => nat end :=
  match v in vec _ m return match m with 0 => unit | S _ => nat end with
  | vnil => tt | vcons _ _ => 5 end.
Goal dep (unk : vec bool 2) = unk. Proof. reflexivity. Qed.
Goal dep (raise : vec bool 0) = raise. Proof. reflexivity. Qed.

Definition len {A n} (v : vec A n) : nat :=
  match v with vnil => 0 | vcons _ _ => 1 end.
Goal len (unk : vec nat 3) = unk. Proof. reflexivity. Qed.

Definition pack {A n} (v : vec A n) : {m : nat & vec A m} :=
  match v with vnil => existT _ 0 vnil | vcons x t => existT _ _ (vcons x t) end.
Goal projT1 (pack (unk : vec nat 3)) = unk. Proof. reflexivity. Qed.
