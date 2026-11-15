(** Kernel conversion laws for the actual gradual primitives, on the
    closed type shapes used in Pantheon's dynamic fields. These are not
    a general extraction/simulation theorem. They use the trusted gradual
    kernel primitives; no new axiom or admitted evidence is introduced. *)
From Stdlib Require Import List Strings.String.
From Corelib Require Import Gradual.Gradual.

Lemma nat_roundtrip : forall n : nat, cast Any nat (cast nat Any n) = n.
Proof. intro n. reflexivity. Qed.
Lemma bool_roundtrip : forall b : bool, cast Any bool (cast bool Any b) = b.
Proof. intro b. reflexivity. Qed.
Lemma list_nat_roundtrip : forall xs : list nat,
  cast Any (list nat) (cast (list nat) Any xs) = xs.
Proof. intro xs. reflexivity. Qed.
Lemma string_roundtrip : forall s : string, cast Any string (cast string Any s) = s.
Proof. intro s. reflexivity. Qed.
Lemma nat_to_bool_fails : forall n : nat,
  cast Any bool (cast nat Any n) = err bool.
Proof. intro n. reflexivity. Qed.
Lemma unknown_stays_unknown : cast Any nat (unknown Any) = unknown nat.
Proof. reflexivity. Qed.
Lemma error_stays_error : cast Any nat (err Any) = err nat.
Proof. reflexivity. Qed.
Lemma option_nat_roundtrip : forall x : option nat,
  cast Any (option nat) (cast (option nat) Any x) = x.
Proof. intro x. reflexivity. Qed.
Lemma pair_roundtrip : forall x : nat * string,
  cast Any (nat * string) (cast (nat * string) Any x) = x.
Proof. intro x. reflexivity. Qed.
Lemma function_roundtrip : forall (f : nat -> nat) x,
  cast Any (nat -> nat) (cast (nat -> nat) Any f) x = f x.
Proof. intros f x. reflexivity. Qed.

(** A runtime-varying tag keeps both paths live in extracted programs. *)
From Stdlib Require Import Arith.
Definition tagged (n : nat) : Any :=
  if Nat.even n then cast nat Any n else cast bool Any true.
(** Mismatched tags below are intentional negative cases. Keep proof
    evidence diagnostics enabled; suppress only this expected warning. *)
Local Set Warnings "-gradual-may-fail".
Definition unpack_nat (n : nat) : nat := cast Any nat (tagged n).
Definition unpack_bool (n : nat) : bool := cast Any bool (tagged n).

Lemma bool_to_nat_fails : forall b : bool,
  cast Any nat (cast bool Any b) = err nat.
Proof. intro b. reflexivity. Qed.
Lemma tagged_nat_even : forall n, Nat.even n = true -> unpack_nat n = n.
Proof. intros n E. unfold unpack_nat, tagged. unfold Nat.even in E. rewrite E. reflexivity. Qed.
Lemma tagged_nat_odd : forall n, Nat.even n = false -> unpack_nat n = err nat.
Proof. intros n E. unfold unpack_nat, tagged. unfold Nat.even in E. rewrite E. reflexivity. Qed.
Lemma tagged_bool_even : forall n, Nat.even n = true -> unpack_bool n = err bool.
Proof. intros n E. unfold unpack_bool, tagged. unfold Nat.even in E. rewrite E. reflexivity. Qed.
Lemma tagged_bool_odd : forall n, Nat.even n = false -> unpack_bool n = true.
Proof. intros n E. unfold unpack_bool, tagged. unfold Nat.even in E. rewrite E. reflexivity. Qed.
