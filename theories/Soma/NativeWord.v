(** Checked indices for Native's signed 63-bit carrier. These definitions use
    the existing Corelib bit interpretation, not new arithmetic axioms. Native
    extraction/compiler correctness remains a separate refinement obligation.
    Test bounds before converting to unary naturals: even an invalid max_int
    index must not construct a gigantic logical natural. *)
From Corelib Require Import PrimInt63 Uint63Axioms Sint63Axioms.
From Stdlib Require Import ZArith Lia Bool.

Definition signed (value : PrimInt63.int) : Z := Sint63Axioms.to_Z value.
Definition of_nat (value : nat) : PrimInt63.int := Uint63Axioms.of_Z (Z.of_nat value).
Definition bounded_index (value : PrimInt63.int) (count : nat) : option nat :=
  let index := signed value in
  if (Z.leb 0 index && Z.ltb index (Z.of_nat count))%bool
  then Some (Z.to_nat index) else None.

(** The OCaml 64-bit runtime profile used by Kykeon. These are native object
    representation bounds, not additional runtime fuel/input caps. Native and
    bytecode conformance tests check the actual Sys values. Physical allocation
    failure below these limits is not excluded by representability. *)
Definition array_limit : Z := (2 ^ 54 - 1)%Z.
Definition string_limit : Z := (2 ^ 57 - 9)%Z.

Theorem bounded_index_sound value count position :
  bounded_index value count = Some position ->
  signed value = Z.of_nat position /\ position < count.
Proof.
  unfold bounded_index. destruct (Z.leb 0 (signed value) && Z.ltb (signed value) (Z.of_nat count))%bool eqn:H;
    intro E; [|discriminate].
  apply andb_true_iff in H. destruct H as [Hnonneg Hbound].
  apply Z.leb_le in Hnonneg. apply Z.ltb_lt in Hbound.
  inversion E; subst. split; [now rewrite Z2Nat.id|].
  apply Nat2Z.inj_lt. now rewrite Z2Nat.id.
Qed.

Theorem bounded_index_complete value count position :
  signed value = Z.of_nat position -> position < count ->
  bounded_index value count = Some position.
Proof.
  intros E Hbound. unfold bounded_index. rewrite E.
  assert (Z.leb 0 (Z.of_nat position) = true) as Hnonneg
    by (apply Z.leb_le; apply Nat2Z.is_nonneg).
  rewrite Hnonneg.
  assert (Z.ltb (Z.of_nat position) (Z.of_nat count) = true) as Hlt
    by (apply Z.ltb_lt; now apply Nat2Z.inj_lt).
  rewrite Hlt. cbn. now rewrite Nat2Z.id.
Qed.

Theorem bounded_index_negative value count :
  (signed value < 0)%Z -> bounded_index value count = None.
Proof.
  intro H. unfold bounded_index.
  assert (Z.leb 0 (signed value) = false) as E by (apply Z.leb_gt; lia).
  now rewrite E.
Qed.

Theorem bounded_index_past_end value count :
  (Z.of_nat count <= signed value)%Z -> bounded_index value count = None.
Proof.
  intro H. unfold bounded_index.
  assert (Z.ltb (signed value) (Z.of_nat count) = false) as E by (apply Z.ltb_ge; exact H).
  rewrite E, andb_false_r. reflexivity.
Qed.

Theorem bounded_index_empty value : bounded_index value 0 = None.
Proof.
  destruct (Z_lt_ge_dec (signed value) 0).
  - now apply bounded_index_negative.
  - apply bounded_index_past_end. lia.
Qed.
