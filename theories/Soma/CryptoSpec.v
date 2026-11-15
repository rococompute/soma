(** Arithmetic invariants for the actual 31-bit limb implementation.
    These depend on Rocq's primitive Uint63 specification, not new axioms.
    Montgomery reduction, SHA-256 and primality are separate obligations. *)
From Stdlib Require Import Uint63 ZArith Lia List.
Require Import Soma.Crypto.
Import ListNotations.
Local Open Scope Z_scope.

Module LimbSpec.
Definition radix : Z := 2147483648.
Definition word := Uint63Axioms.to_Z.
Definition limb (x : int) : Prop := 0 <= word x < radix.
Fixpoint value (xs : list int) : Z :=
  match xs with [] => 0 | x :: rest => word x + radix * value rest end.

Lemma low31 : forall x, word (PrimInt63.land x Bignum.mask31) = word x mod radix.
Proof.
  intro x. unfold word. rewrite Uint63.land_spec'.
  change (Z.land (Uint63Axioms.to_Z x) (Z.ones 31) = Uint63Axioms.to_Z x mod radix).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma high31 : forall x, word (PrimInt63.lsr x 31%uint63) = word x / radix.
Proof. intro x. unfold word. rewrite Uint63Axioms.lsr_spec. reflexivity. Qed.

Lemma split31 : forall x,
  word (PrimInt63.land x Bignum.mask31) +
  radix * word (PrimInt63.lsr x 31%uint63) = word x.
Proof.
  intro x. rewrite low31, high31.
  pose proof (Z.div_mod (word x) radix ltac:(unfold radix; lia)). lia.
Qed.

Lemma low31_limb : forall x, limb (PrimInt63.land x Bignum.mask31).
Proof. intro x. unfold limb. rewrite low31. apply Z.mod_pos_bound. unfold radix; lia. Qed.

Lemma word_add_exact : forall x y,
  word x + word y < 9223372036854775808 ->
  word (PrimInt63.add x y) = word x + word y.
Proof.
  intros x y H. unfold word in *. rewrite Uint63Axioms.add_spec.
  apply Z.mod_small. pose proof (Uint63.to_Z_bounded x).
  pose proof (Uint63.to_Z_bounded y). change (0 <= Uint63Axioms.to_Z x + Uint63Axioms.to_Z y < 9223372036854775808). lia.
Qed.

Lemma word_mul_exact : forall x y,
  word x * word y < 9223372036854775808 ->
  word (PrimInt63.mul x y) = word x * word y.
Proof.
  intros x y H. unfold word in *. rewrite Uint63Axioms.mul_spec.
  apply Z.mod_small. pose proof (Uint63.to_Z_bounded x).
  pose proof (Uint63.to_Z_bounded y). change (0 <= Uint63Axioms.to_Z x * Uint63Axioms.to_Z y < 9223372036854775808). nia.
Qed.

Lemma carry_of_sum : forall x c,
  limb x -> limb c -> limb (PrimInt63.lsr (PrimInt63.add x c) 31%uint63).
Proof.
  intros x c Hx Hc. unfold limb in *. rewrite high31.
  rewrite word_add_exact by (unfold radix in *; lia).
  split.
  - apply Z.div_pos; unfold radix in *; lia.
  - apply Z.div_lt_upper_bound; unfold radix in *; nia.
Qed.

Theorem add_carry1_correct : forall xs c,
  Forall limb xs -> limb c ->
  value (Bignum.add_carry1 xs c) = value xs + word c /\
  Forall limb (Bignum.add_carry1 xs c).
Proof.
  induction xs as [|x xs IH]; intros c Hxs Hc; inversion Hxs; subst.
  - cbn [Bignum.add_carry1]. destruct (PrimInt63.eqb c 0%uint63) eqn:E.
    + apply Uint63Axioms.eqb_correct in E. subst c. split; [reflexivity|constructor].
    + split; [cbn [value]; lia|constructor; [exact Hc|constructor]].
  - cbn [Bignum.add_carry1].
    destruct (IH (PrimInt63.lsr (PrimInt63.add x c) 31%uint63) H2
      (carry_of_sum x c H1 Hc)) as [E Bound].
    split.
    + cbn [value]. rewrite E. pose proof (split31 (PrimInt63.add x c)).
      rewrite word_add_exact in H by (unfold limb, radix in *; lia). lia.
    + constructor; [apply low31_limb|exact Bound].
Qed.

Theorem add_carry_correct : forall xs ys c,
  Forall limb xs -> Forall limb ys -> limb c ->
  value (Bignum.add_carry xs ys c) = value xs + value ys + word c /\
  Forall limb (Bignum.add_carry xs ys c).
Proof.
  induction xs as [|x xs IH]; intros ys c Hxs Hys Hc.
  - cbn [Bignum.add_carry value]. apply add_carry1_correct; assumption.
  - destruct ys as [|y ys].
    + cbn [Bignum.add_carry]. destruct (add_carry1_correct (x :: xs) c Hxs Hc) as [E B].
      split; [cbn [value] in *; lia|exact B].
    + inversion Hxs as [|? ? Hx Hxs']; subst.
      inversion Hys as [|? ? Hy Hys']; subst.
      assert (Esum : word (PrimInt63.add (PrimInt63.add x y) c) = word x + word y + word c).
      { rewrite word_add_exact.
        - rewrite word_add_exact; unfold limb, radix in *; lia.
        - rewrite word_add_exact; unfold limb, radix in *; lia. }
      assert (Carry : limb (PrimInt63.lsr (PrimInt63.add (PrimInt63.add x y) c) 31%uint63)).
      { unfold limb. rewrite high31, Esum. split.
        - apply Z.div_pos; unfold limb, radix in *; lia.
        - apply Z.div_lt_upper_bound; unfold limb, radix in *; nia. }
      cbn [Bignum.add_carry]. destruct (IH ys _ Hxs' Hys' Carry) as [E B]. split.
      * cbn [value]. rewrite E.
        pose proof (split31 (PrimInt63.add (PrimInt63.add x y) c)). rewrite Esum in H. lia.
      * constructor; [apply low31_limb|exact B].
Qed.

Theorem mul_limb_correct : forall xs x c,
  Forall limb xs -> limb x -> limb c ->
  value (Bignum.mul_limb xs x c) = word x * value xs + word c /\
  Forall limb (Bignum.mul_limb xs x c).
Proof.
  induction xs as [|y xs IH]; intros x c Hxs Hx Hc.
  - cbn [Bignum.mul_limb value]. split; [lia|constructor; [exact Hc|constructor]].
  - inversion Hxs as [|? ? Hy Hxs']; subst.
    assert (Eprod : word (PrimInt63.add (PrimInt63.mul x y) c) = word x * word y + word c).
    { rewrite word_add_exact.
      - rewrite word_mul_exact; unfold limb, radix in *; nia.
      - rewrite word_mul_exact; unfold limb, radix in *; nia. }
    assert (Carry : limb (PrimInt63.lsr (PrimInt63.add (PrimInt63.mul x y) c) 31%uint63)).
    { unfold limb. rewrite high31, Eprod. split.
      - apply Z.div_pos; unfold limb, radix in *; nia.
      - apply Z.div_lt_upper_bound; unfold limb, radix in *; nia. }
    cbn [Bignum.mul_limb]. destruct (IH x _ Hxs' Hx Carry) as [E B]. split.
    + cbn [value]. rewrite E.
      pose proof (split31 (PrimInt63.add (PrimInt63.mul x y) c)). rewrite Eprod in H. nia.
    + constructor; [apply low31_limb|exact B].
Qed.

Theorem mul_big_correct : forall xs ys,
  Forall limb xs -> Forall limb ys ->
  value (Bignum.mul_big xs ys) = value xs * value ys /\
  Forall limb (Bignum.mul_big xs ys).
Proof.
  induction xs as [|x xs IH]; intros ys Hxs Hys.
  - cbn [Bignum.mul_big value]. split; [lia|constructor].
  - inversion Hxs as [|? ? Hx Hxs']; subst.
    assert (Zero : limb 0%uint63) by (unfold limb, word, radix; vm_compute; easy).
    destruct (IH ys Hxs' Hys) as [E B].
    destruct (mul_limb_correct ys x 0%uint63 Hys Hx Zero) as [E1 B1].
    assert (Shift : Forall limb (0%uint63 :: Bignum.mul_big xs ys)) by (constructor; assumption).
    destruct (add_carry_correct _ _ 0%uint63 B1 Shift Zero) as [E2 B2].
    cbn [Bignum.mul_big]. split; [|exact B2].
    rewrite E2. cbn [value]. rewrite E, E1. change (word 0%uint63) with 0. cbn [value]. ring.
Qed.
Lemma value_append : forall xs ys,
  value (xs ++ ys) = value xs + radix ^ Z.of_nat (length xs) * value ys.
Proof.
  induction xs as [|x xs IH]; intro ys; cbn [List.app value List.length].
  - change (value ys = 0 + 1 * value ys). ring.
  - rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma drop_high_zeros : forall xs,
  value (rev (Bignum.drop_zeros xs)) = value (rev xs).
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  cbn [Bignum.drop_zeros]. destruct (PrimInt63.eqb x 0%uint63) eqn:E.
  - apply Uint63Axioms.eqb_correct in E. subst x. rewrite IH.
    cbn [List.rev]. rewrite value_append. cbn [value]. change (word 0%uint63) with 0. ring.
  - reflexivity.
Qed.

Theorem trim_preserves_value : forall xs, value (Bignum.trim xs) = value xs.
Proof. intro xs. unfold Bignum.trim. rewrite drop_high_zeros, rev_involutive. reflexivity. Qed.
End LimbSpec.
