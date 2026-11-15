(** Contracts for the native [nat] realization used by both backends.

    [signed] is the mathematical signed-word operation. These theorems
    are conditional refinement results: they do not claim that unbounded
    naturals fit in a machine integer, nor prove Pantheon's range invariants.
    The native backend conformance test exercises the actual extracted
    operations, including values near [max_int]. *)
From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

Module Native.
Definition fits (half value : Z) : Prop := 0 <= value < half.
Definition signed (half value : Z) : Z := (value + half) mod (2 * half) - half.
Definition add (half a b : Z) : Z := signed half (a + b).
Definition mul (half a b : Z) : Z := signed half (a * b).
Definition sub (half a b : Z) : Z := Z.max 0 (signed half (a - b)).

Theorem signed_exact : forall half value,
  0 < half -> -half <= value < half -> signed half value = value.
Proof.
  intros half value Hhalf Hvalue. unfold signed.
  rewrite Z.mod_small by lia. lia.
Qed.

Theorem add_refines : forall half a b,
  fits half a -> fits half b -> a + b < half -> add half a b = a + b.
Proof.
  intros half a b Ha Hb Hsum. unfold add. apply signed_exact; unfold fits in *; lia.
Qed.

Theorem mul_refines : forall half a b,
  fits half a -> fits half b -> a * b < half -> mul half a b = a * b.
Proof.
  intros half a b Ha Hb Hproduct. unfold mul. apply signed_exact; unfold fits in *; nia.
Qed.

Theorem sub_refines : forall half a b,
  fits half a -> fits half b -> sub half a b = Z.max 0 (a - b).
Proof.
  intros half a b Ha Hb. unfold sub. rewrite signed_exact; unfold fits in *; lia.
Qed.

(** Guards can be evaluated without first overflowing the operation they
    guard. A bound on each input alone is insufficient for addition/mul. *)
Theorem add_guard : forall half a b,
  fits half a -> fits half b -> (a + b < half <-> a <= half - 1 - b).
Proof. unfold fits; intros; lia. Qed.

Theorem mul_guard : forall half a b,
  fits half a -> fits half b -> 0 < b ->
  (a * b < half <-> a <= (half - 1) / b).
Proof.
  unfold fits. intros half a b Ha Hb Hpositive.
  pose proof (Z.div_mod (half - 1) b ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound (half - 1) b Hpositive) as Hrem.
  split; intro H; nia.
Qed.

Theorem add_overflow_is_not_nat_add : forall half,
  0 < half -> add half (half - 1) 1 = -half.
Proof.
  intros half H. unfold add, signed. replace (half - 1 + 1 + half) with (2 * half) by lia.
  rewrite Z.mod_same by lia. lia.
Qed.

Definition half64 : Z := 4611686018427387904.
Theorem decimal18_fits64 : forall n,
  0 <= n < 1000000000000000000 -> fits half64 n.
Proof. unfold fits, half64; intros; lia. Qed.

Theorem decimal18_product_needs_another_bound :
  fits half64 999999999999999999 /\
  ~ fits half64 (999999999999999999 * 999999999999999999).
Proof. unfold fits, half64; lia. Qed.
End Native.
