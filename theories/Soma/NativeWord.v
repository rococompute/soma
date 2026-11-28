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
Definition nat_fits (value : nat) := (Z.of_nat value <= 2 ^ 62 - 1)%Z.

(** The sum lives in Z, not in wrapping machine arithmetic. Convert neither
    argument to unary naturals until both signs and the whole span are checked.
    For representable strings this is equivalent to OCaml's safe subtraction
    check [offset > length - count], including the empty slice at the end. *)
Definition bounded_slice (offset count : PrimInt63.int) (length : nat) : option (nat * nat) :=
  let start := signed offset in let size := signed count in
  if (Z.leb 0 start && Z.leb 0 size && Z.leb (start + size) (Z.of_nat length))%bool
  then Some (Z.to_nat start, Z.to_nat size) else None.

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

Theorem bounded_slice_sound offset count length start size :
  bounded_slice offset count length = Some (start, size) ->
  signed offset = Z.of_nat start /\ signed count = Z.of_nat size /\ start + size <= length.
Proof.
  unfold bounded_slice.
  destruct (Z.leb 0 (signed offset) && Z.leb 0 (signed count) &&
    Z.leb (signed offset + signed count) (Z.of_nat length))%bool eqn:Guard;
    intro Equal; [|discriminate].
  repeat rewrite andb_true_iff in Guard. destruct Guard as [[Start Size] Bound].
  apply Z.leb_le in Start, Size, Bound. inversion Equal; subst.
  split; [symmetry; now apply Z2Nat.id|].
  split; [symmetry; now apply Z2Nat.id|].
  apply Nat2Z.inj_le. rewrite Nat2Z.inj_add.
  rewrite !Z2Nat.id by assumption. exact Bound.
Qed.

Theorem bounded_slice_complete offset count length start size :
  signed offset = Z.of_nat start -> signed count = Z.of_nat size -> start + size <= length ->
  bounded_slice offset count length = Some (start, size).
Proof.
  intros Start Size Bound. unfold bounded_slice. rewrite Start, Size.
  assert (Z.leb 0 (Z.of_nat start) = true) as S0 by (apply Z.leb_le; lia).
  assert (Z.leb 0 (Z.of_nat size) = true) as N0 by (apply Z.leb_le; lia).
  assert (Z.leb (Z.of_nat start + Z.of_nat size) (Z.of_nat length) = true) as Fits
    by (apply Z.leb_le; lia).
  rewrite S0, N0, Fits. cbn. now rewrite !Nat2Z.id.
Qed.

Theorem bounded_slice_negative_offset offset count length :
  (signed offset < 0)%Z -> bounded_slice offset count length = None.
Proof.
  intro Negative. unfold bounded_slice.
  assert (Z.leb 0 (signed offset) = false) as Bad by (apply Z.leb_gt; exact Negative).
  now rewrite Bad.
Qed.

Theorem bounded_slice_negative_count offset count length :
  (signed count < 0)%Z -> bounded_slice offset count length = None.
Proof.
  intro Negative. unfold bounded_slice.
  assert (Z.leb 0 (signed count) = false) as Bad by (apply Z.leb_gt; exact Negative).
  now rewrite Bad, andb_false_r.
Qed.

Theorem bounded_slice_past_end offset count length :
  (Z.of_nat length < signed offset + signed count)%Z -> bounded_slice offset count length = None.
Proof.
  intro Beyond. unfold bounded_slice.
  assert (Z.leb (signed offset + signed count) (Z.of_nat length) = false) as Bad
    by (apply Z.leb_gt; exact Beyond).
  now rewrite Bad, andb_false_r.
Qed.
