(** Source IPv4 parsing and CIDR geometry. Addresses use binary Z, avoiding
    both overflowing machine arithmetic and enormous logical unary naturals.
    Decimal accumulation explicitly models the existing 63-bit parser wrap;
    no input-length cap or silent rejection of legacy wrapped spellings is
    introduced. Production integration is separate from this library. *)
(** Parser compatibility behavior is adapted from ipaddr, whose notice follows.
    Copyright (c) 2013-2015 David Sheets <sheets@alum.mit.edu>

    Permission to use, copy, modify, and distribute this software for any
    purpose with or without fee is hereby granted, provided that the above
    copyright notice and this permission notice appear in all copies.

    THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
    WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
    MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
    ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
    WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
    ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
    OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. *)
From Stdlib Require Import ZArith Lia Strings.String Strings.Ascii Arith.PeanoNat List.
Import ListNotations.
Local Open Scope Z_scope.
Set Implicit Arguments.

Definition address_limit : Z := 4294967296.
Definition parser_modulus : Z := 9223372036854775808.
Record address := Address { value : Z; value_range : 0 <= value < address_limit }.
Record prefix := Prefix { network : address; bits : nat; bits_range : (bits <= 32)%nat }.
Definition block_size width : Z := 2 ^ Z.of_nat (32 - width).
Definition network_base p := (value (network p) / block_size (bits p)) * block_size (bits p).
Definition contains (p : prefix) (ip : address) :=
  Z.eqb (value ip / block_size (bits p)) (value (network p) / block_size (bits p)).

Theorem block_size_positive width : 0 < block_size width.
Proof. unfold block_size. apply Z.pow_pos_nonneg; lia. Qed.

Theorem block_size_bound width : block_size width <= address_limit.
Proof.
  unfold block_size, address_limit. change (2 ^ Z.of_nat (32 - width) <= 2 ^ 32).
  apply Z.pow_le_mono_r; lia.
Qed.

Theorem contains_iff_interval p ip :
  contains p ip = true <-> network_base p <= value ip < network_base p + block_size (bits p).
Proof.
  unfold contains, network_base. rewrite Z.eqb_eq.
  pose proof (block_size_positive (bits p)) as Positive.
  pose proof (Z.div_mod (value ip) (block_size (bits p)) ltac:(lia)) as Decompose.
  pose proof (Z.mod_pos_bound (value ip) (block_size (bits p)) Positive) as Remainder.
  split.
  - intro Same. rewrite Same in Decompose. nia.
  - intro Interval. symmetry. apply Z.div_unique with
      (r := value ip - block_size (bits p) * (value (network p) / block_size (bits p))); nia.
Qed.

Theorem network_base_aligned p : network_base p mod block_size (bits p) = 0.
Proof.
  unfold network_base. rewrite Z.mul_mod by (pose proof (block_size_positive (bits p)); lia).
  rewrite Z.mod_same by (pose proof (block_size_positive (bits p)); lia).
  rewrite Z.mul_0_r. apply Z.mod_0_l. pose proof (block_size_positive (bits p)); lia.
Qed.

Theorem network_is_contained p : contains p (network p) = true.
Proof. unfold contains. apply Z.eqb_refl. Qed.

Theorem zero_prefix_all p ip : bits p = 0%nat -> contains p ip = true.
Proof.
  intro Width. unfold contains. rewrite Width. change (Z.eqb (value ip / address_limit) (value (network p) / address_limit) = true).
  rewrite !Z.div_small by apply value_range. reflexivity.
Qed.

Theorem full_prefix_exact p ip : bits p = 32%nat ->
  (contains p ip = true <-> value ip = value (network p)).
Proof. intro Width. unfold contains. rewrite Width. cbn [block_size]. now rewrite !Z.div_1_r, Z.eqb_eq. Qed.

Theorem block_size_refines small large : (small <= large <= 32)%nat ->
  block_size small = block_size large * 2 ^ Z.of_nat (large - small).
Proof.
  intros Order. unfold block_size.
  replace (Z.of_nat (32 - small)) with (Z.of_nat (32 - large) + Z.of_nat (large - small)) by lia.
  apply Z.pow_add_r; lia.
Qed.

Lemma quotient_refines number divisor factor : 0 < divisor -> 0 < factor ->
  number / (divisor * factor) = (number / divisor) / factor.
Proof. intros. symmetry. apply Z.div_div; lia. Qed.

Theorem subnet_contains_subsets coarse fine ip :
  (bits coarse <= bits fine)%nat -> contains coarse (network fine) = true ->
  contains fine ip = true -> contains coarse ip = true.
Proof.
  intros Width Network Inside. unfold contains in *.
  apply Z.eqb_eq in Network, Inside. apply Z.eqb_eq.
  rewrite (block_size_refines (small:=bits coarse) (large:=bits fine)) in * by
    (split; [exact Width|apply bits_range]).
  rewrite !quotient_refines in * by
    (first [apply block_size_positive|apply Z.pow_pos_nonneg; lia]).
  now rewrite Inside.
Qed.

Theorem separated_prefixes_do_not_overlap left right ip :
  network_base left + block_size (bits left) <= network_base right ->
  contains left ip = true -> contains right ip = false.
Proof.
  intros Separate Inside. apply contains_iff_interval in Inside.
  destruct (contains right ip) eqn:Other; [|reflexivity].
  apply contains_iff_interval in Other. lia.
Qed.

Definition address_bytes ip : list nat :=
  [Z.to_nat (value ip / 16777216); Z.to_nat ((value ip / 65536) mod 256);
   Z.to_nat ((value ip / 256) mod 256); Z.to_nat (value ip mod 256)].

Definition make_prefix (ip : address) (width : nat) : option prefix.
Proof. destruct (le_dec width 32) as [Bound|Invalid]; [exact (Some (@Prefix ip width Bound))|exact None]. Defined.

Inductive failure := Need_more | Bad_character (character : ascii) (position : nat)
  | Octal_notation | Octet_bounds (ordinal : nat) | Invalid_prefix_size.
Inductive read (A : Type) := Ready (item : A) (position : nat) | Failed (reason : failure).
Arguments Ready {A} item position.
Arguments Failed {A} reason.
Definition bind {A B} (input : read A) (next : A -> nat -> read B) : read B :=
  match input with Ready item position => next item position | Failed reason => Failed reason end.

Definition digit (character : ascii) : option Z :=
  if Ascii.eqb character "0"%char then Some 0 else
  if Ascii.eqb character "1"%char then Some 1 else
  if Ascii.eqb character "2"%char then Some 2 else
  if Ascii.eqb character "3"%char then Some 3 else
  if Ascii.eqb character "4"%char then Some 4 else
  if Ascii.eqb character "5"%char then Some 5 else
  if Ascii.eqb character "6"%char then Some 6 else
  if Ascii.eqb character "7"%char then Some 7 else
  if Ascii.eqb character "8"%char then Some 8 else
  if Ascii.eqb character "9"%char then Some 9 else None.
Definition roll accumulator next := (10 * accumulator + next) mod parser_modulus.

Fixpoint digits (text : string) (remaining cursor : nat) (accumulator : Z) : read Z :=
  match remaining with
  | O => Ready accumulator cursor
  | S rest => match String.get cursor text with
    | None => Ready accumulator cursor
    | Some character => match digit character with
      | None => Ready accumulator cursor
      | Some next => digits text rest (S cursor) (roll accumulator next)
      end
    end
  end.
Definition decimal text cursor : read Z :=
  match String.get cursor text with
  | None => Failed Need_more
  | Some character => match digit character with
    | None => Failed (Bad_character character cursor)
    | Some first => digits text (String.length text - S cursor) (S cursor) first
    end
  end.
Definition octet text cursor : read Z :=
  match String.get cursor text, String.get (S cursor) text with
  | Some first, Some second =>
      if Ascii.eqb first "0"%char then
        match digit second with Some _ => Failed Octal_notation | None => decimal text cursor end
      else decimal text cursor
  | _, _ => decimal text cursor
  end.
Definition expect text cursor character : read unit :=
  match String.get cursor text with
  | None => Failed Need_more
  | Some actual => if Ascii.eqb actual character then Ready tt (S cursor)
      else Failed (Bad_character actual cursor)
  end.

Definition assemble a b c d (A : 0 <= a <= 255) (B : 0 <= b <= 255)
    (C : 0 <= c <= 255) (D : 0 <= d <= 255) : address.
Proof. refine (@Address (((a * 256 + b) * 256 + c) * 256 + d) _).
  unfold address_limit. lia.
Defined.
Definition checked_quad (a b c d : Z) (cursor : nat) : read address.
Proof.
  destruct (Z_le_dec 0 a), (Z_le_dec a 255); [|exact (Failed (Octet_bounds 1))..].
  destruct (Z_le_dec 0 b), (Z_le_dec b 255); [|exact (Failed (Octet_bounds 2))..].
  destruct (Z_le_dec 0 c), (Z_le_dec c 255); [|exact (Failed (Octet_bounds 3))..].
  destruct (Z_le_dec 0 d), (Z_le_dec d 255); [|exact (Failed (Octet_bounds 4))..].
  exact (Ready (@assemble a b c d ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) cursor).
Defined.
Definition quad text cursor : read address :=
  bind (octet text cursor) (fun a cursor => bind (expect text cursor "."%char) (fun _ cursor =>
  bind (octet text cursor) (fun b cursor => bind (expect text cursor "."%char) (fun _ cursor =>
  bind (octet text cursor) (fun c cursor => bind (expect text cursor "."%char) (fun _ cursor =>
  bind (octet text cursor) (fun d cursor => checked_quad a b c d cursor))))))).
Definition checked_prefix (ip : address) (width : Z) (cursor : nat) : read prefix.
Proof.
  destruct (Z_le_dec 0 width), (Z_le_dec width 32); [|exact (Failed Invalid_prefix_size)..].
  refine (Ready (@Prefix ip (Z.to_nat width) _) cursor).
  apply Nat2Z.inj_le. rewrite Z2Nat.id by assumption. exact l0.
Defined.
Definition prefix_read text cursor :=
  bind (quad text cursor) (fun ip cursor => bind (expect text cursor "/"%char) (fun _ cursor =>
  bind (decimal text cursor) (fun width cursor => checked_prefix ip width cursor))).
Definition finish {A} text (input : read A) : read A :=
  bind input (fun item cursor => match String.get cursor text with
    | None => Ready item cursor | Some character => Failed (Bad_character character cursor) end).
Definition of_string text := finish text (quad text 0%nat).
Definition prefix_of_string text := finish text (prefix_read text 0%nat).

Theorem digit_range character number : digit character = Some number -> 0 <= number < 10.
Proof.
  unfold digit. repeat match goal with |- context[if ?guard then _ else _] => destruct guard end;
    intro Equal; inversion Equal; lia.
Qed.

Theorem roll_range accumulator next : 0 <= roll accumulator next < parser_modulus.
Proof. unfold roll. apply Z.mod_pos_bound. reflexivity. Qed.

Theorem digits_value_range text remaining : forall cursor accumulator number final,
  0 <= accumulator < parser_modulus -> digits text remaining cursor accumulator = Ready number final ->
  0 <= number < parser_modulus.
Proof.
  induction remaining as [|remaining IH]; intros cursor accumulator number final Range Read; cbn in Read.
  - inversion Read; subst; assumption.
  - destruct (String.get cursor text) as [character|]; [destruct (digit character)|];
      try (inversion Read; subst; assumption).
    eapply IH; [apply roll_range|exact Read].
Qed.

Theorem digits_cursor_bounds text remaining : forall cursor accumulator number final,
  digits text remaining cursor accumulator = Ready number final ->
  (cursor <= final <= cursor + remaining)%nat.
Proof.
  induction remaining as [|remaining IH]; intros cursor accumulator number final Read; cbn in Read.
  - inversion Read; subst; lia.
  - destruct (String.get cursor text) as [character|]; [destruct (digit character)|];
      try (inversion Read; subst; lia).
    apply IH in Read. lia.
Qed.

Theorem decimal_value_range text cursor number final :
  decimal text cursor = Ready number final -> 0 <= number < parser_modulus.
Proof.
  unfold decimal. destruct (String.get cursor text) as [character|]; [destruct (digit character) eqn:Digit|];
    intro Read; try discriminate.
  eapply digits_value_range; [|exact Read]. apply digit_range in Digit.
  unfold parser_modulus. lia.
Qed.
