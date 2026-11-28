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
From Stdlib Require Import ZArith Lia Strings.String Strings.Ascii Arith.PeanoNat List Bool.Bool.
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

Definition decimal_character character number :=
  (48 <= nat_of_ascii character <= 57)%nat /\
  number = Z.of_nat (nat_of_ascii character - 48).

Lemma digit_code character :
  digit character =
    if andb (Nat.leb 48 (nat_of_ascii character)) (Nat.leb (nat_of_ascii character) 57)
    then Some (Z.of_nat (nat_of_ascii character - 48)) else None.
Proof.
  destruct character as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; reflexivity.
Qed.

Theorem digit_character_iff character number :
  digit character = Some number <-> decimal_character character number.
Proof.
  rewrite digit_code. unfold decimal_character.
  destruct (andb (Nat.leb 48 (nat_of_ascii character)) (Nat.leb (nat_of_ascii character) 57)) eqn:Decimal.
  - apply Bool.andb_true_iff in Decimal as [Lower Upper].
    apply Nat.leb_le in Lower, Upper. split.
    + intro Same. injection Same as <-. split; [lia|reflexivity].
    + intros [_ ->]. reflexivity.
  - split; [discriminate|]. intros [Bounds _].
    assert (andb (Nat.leb 48 (nat_of_ascii character)) (Nat.leb (nat_of_ascii character) 57) = true)
      by (apply Bool.andb_true_iff; split; apply Nat.leb_le; lia).
    congruence.
Qed.

Theorem digit_none_iff character :
  digit character = None <-> forall number, ~ decimal_character character number.
Proof.
  split.
  - intros No_digit number Character. apply digit_character_iff in Character. congruence.
  - intro No_character. destruct (digit character) as [number|] eqn:Digit; [|reflexivity].
    exfalso. apply (No_character number). now apply digit_character_iff.
Qed.

(** The grammar is specified by the actual bytes and a left fold of their
    decimal values, independently of the scanner's recursion budget. The
    fold deliberately uses the documented legacy modular accumulation. *)
Fixpoint decimal_bytes (text : string) (cursor : nat) (values : list Z) : Prop :=
  match values with
  | [] => True
  | number :: rest =>
      (exists character, String.get cursor text = Some character /\ decimal_character character number) /\
      decimal_bytes text (S cursor) rest
  end.
Definition decimal_span text begin ending initial number :=
  exists values, ending = (begin + List.length values)%nat /\
    decimal_bytes text begin values /\ fold_left roll values initial = number.
Definition non_decimal_at text cursor :=
  forall character number, String.get cursor text = Some character -> ~ decimal_character character number.

Theorem digits_span text remaining : forall cursor accumulator number final,
  digits text remaining cursor accumulator = Ready number final ->
  decimal_span text cursor final accumulator number.
Proof.
  induction remaining as [|remaining IH]; intros cursor accumulator number final Read; cbn in Read.
  - inversion Read; subst. exists []; cbn. auto.
  - destruct (String.get cursor text) as [character|] eqn:Get;
      [destruct (digit character) as [next|] eqn:Digit|].
    + apply IH in Read. destruct Read as [values [End [Bytes Value]]].
      exists (next :: values). cbn. split; [lia|]. split; [|exact Value].
      split; [exists character; split; [exact Get|now apply digit_character_iff]|exact Bytes].
    + inversion Read; subst. exists []; cbn. auto.
    + inversion Read; subst. exists []; cbn. auto.
Qed.

Theorem digits_stop text remaining : forall cursor accumulator number final,
  digits text remaining cursor accumulator = Ready number final ->
  final = (cursor + remaining)%nat \/ non_decimal_at text final.
Proof.
  induction remaining as [|remaining IH]; intros cursor accumulator number final Read; cbn in Read.
  - inversion Read; subst. left. lia.
  - destruct (String.get cursor text) as [character|] eqn:Get;
      [destruct (digit character) as [next|] eqn:Digit|].
    + apply IH in Read. destruct Read as [End|Stop]; [left; lia|right; exact Stop].
    + inversion Read; subst. right. intros actual candidate Same Character. rewrite Get in Same.
      injection Same as <-. apply digit_character_iff in Character. congruence.
    + inversion Read; subst. right. intros actual candidate Same. rewrite Get in Same. discriminate.
Qed.

Theorem digits_cannot_fail text remaining : forall cursor accumulator,
  exists number final, digits text remaining cursor accumulator = Ready number final.
Proof.
  induction remaining as [|remaining IH]; intros cursor accumulator; cbn.
  - eauto.
  - destruct (String.get cursor text) as [character|]; [destruct (digit character)|]; eauto.
Qed.

Lemma text_get_some_bound text : forall cursor character,
  String.get cursor text = Some character -> (cursor < String.length text)%nat.
Proof.
  induction text as [|head rest IH]; intros [|cursor] character Read; cbn in *;
    try discriminate; try lia.
  apply IH in Read. lia.
Qed.

Lemma text_get_none_iff text : forall cursor,
  String.get cursor text = None <-> (String.length text <= cursor)%nat.
Proof.
  induction text as [|head rest IH]; intros [|cursor]; cbn;
    try (split; intros; try reflexivity; try discriminate; lia).
  rewrite IH. lia.
Qed.

Theorem digits_consume_bytes text values : forall cursor remaining initial,
  decimal_bytes text cursor values -> (List.length values <= remaining)%nat ->
  non_decimal_at text (cursor + List.length values)%nat ->
  digits text remaining cursor initial = Ready (fold_left roll values initial) (cursor + List.length values)%nat.
Proof.
  induction values as [|next values IH]; intros cursor remaining initial Bytes Bound Stop.
  - cbn in *. replace (cursor + 0)%nat with cursor in * by lia.
    destruct remaining; [reflexivity|]. cbn.
    destruct (String.get cursor text) as [character|] eqn:Get; [|reflexivity].
    destruct (digit character) as [number|] eqn:Digit; [|reflexivity].
    exfalso. apply (Stop character number Get). now apply digit_character_iff.
  - cbn in Bytes, Bound, Stop. destruct Bytes as [[character [Get Digit]] Bytes].
    apply digit_character_iff in Digit.
    destruct remaining as [|remaining]; [lia|]. cbn. rewrite Get, Digit.
    replace (cursor + S (List.length values))%nat with (S cursor + List.length values)%nat in * by lia.
    apply IH; [exact Bytes|lia|exact Stop].
Qed.

Definition decimal_token text cursor final number :=
  (cursor < final <= String.length text)%nat /\
  decimal_span text cursor final 0 number /\ non_decimal_at text final.

Theorem decimal_token_sound text cursor number final :
  decimal text cursor = Ready number final -> decimal_token text cursor final number.
Proof.
  unfold decimal. destruct (String.get cursor text) as [character|] eqn:Get;
    [destruct (digit character) as [first|] eqn:Digit|]; intro Read; try discriminate.
  pose proof (@text_get_some_bound text cursor character Get) as Cursor.
  pose proof (@digits_cursor_bounds text _ _ _ _ _ Read) as Bounds.
  pose proof (@digits_span text _ _ _ _ _ Read) as Span.
  pose proof (@digits_stop text _ _ _ _ _ Read) as Stop.
  apply digit_range in Digit as Range.
  split; [lia|]. split.
  - destruct Span as [values [End [Bytes Value]]]. exists (first :: values).
    cbn. split; [lia|]. split.
    + split; [exists character; split; [exact Get|now apply digit_character_iff]|exact Bytes].
    + change (fold_left roll values (first mod parser_modulus) = number).
      rewrite Z.mod_small; [exact Value|].
      unfold parser_modulus. lia.
  - destruct Stop as [End|Stop]; [|exact Stop].
    assert (final = String.length text) by lia. subst final.
    intros actual candidate Same. apply text_get_some_bound in Same. lia.
Qed.

Theorem decimal_token_complete text cursor number final :
  decimal_token text cursor final number -> decimal text cursor = Ready number final.
Proof.
  intros [Bounds [[values [End [Bytes Value]]] Stop]].
  destruct values as [|first values]; [cbn in End; lia|].
  cbn in Bytes. destruct Bytes as [[character [Get Digit]] Bytes].
  apply digit_character_iff in Digit.
  unfold decimal. rewrite Get, Digit.
  assert (roll 0 first = first) as Initial.
  { unfold roll. rewrite Z.mul_0_r, Z.add_0_l. apply Z.mod_small.
    apply digit_range in Digit. unfold parser_modulus. lia. }
  cbn in Value. rewrite Initial in Value.
  pose proof (@digits_consume_bytes text values (S cursor)
    (String.length text - S cursor) first Bytes ltac:(cbn in End; lia)
    ltac:(replace (S cursor + List.length values)%nat with final by (cbn in End; lia); exact Stop)) as Read.
  rewrite Read, Value. f_equal. cbn in End. lia.
Qed.

Theorem decimal_token_iff text cursor number final :
  decimal text cursor = Ready number final <-> decimal_token text cursor final number.
Proof. split; [apply decimal_token_sound|apply decimal_token_complete]. Qed.

Definition octet_token text cursor final number :=
  decimal_token text cursor final number /\
  (String.get cursor text = Some "0"%char -> forall second,
    String.get (S cursor) text = Some second -> forall number, ~ decimal_character second number).

Lemma octet_decimal text cursor number final :
  octet text cursor = Ready number final -> decimal text cursor = Ready number final.
Proof.
  unfold octet. destruct (String.get cursor text) as [first|];
    destruct (String.get (S cursor) text) as [second|]; try (intro Read; exact Read).
  all: destruct (Ascii.eqb first "0"%char); [destruct (digit second)|];
    intro Read; try discriminate; exact Read.
Qed.

Theorem octet_token_sound text cursor number final :
  octet text cursor = Ready number final -> octet_token text cursor final number.
Proof.
  intro Read. split; [apply decimal_token_sound; now apply octet_decimal|].
  intros Zero second Second. unfold octet in Read. rewrite Zero, Second, Ascii.eqb_refl in Read.
  apply digit_none_iff. destruct (digit second); [discriminate|reflexivity].
Qed.

Theorem octet_token_complete text cursor number final :
  octet_token text cursor final number -> octet text cursor = Ready number final.
Proof.
  intros [Decimal No_octal]. apply decimal_token_complete in Decimal.
  unfold octet. destruct (String.get cursor text) as [first|] eqn:First;
    destruct (String.get (S cursor) text) as [second|] eqn:Second; try exact Decimal.
  destruct (Ascii.eqb first "0"%char) eqn:Zero; [|exact Decimal].
  apply Ascii.eqb_eq in Zero. subst first.
  rewrite (proj2 (digit_none_iff second) (No_octal eq_refl second eq_refl)). exact Decimal.
Qed.

Theorem octet_token_iff text cursor number final :
  octet text cursor = Ready number final <-> octet_token text cursor final number.
Proof. split; [apply octet_token_sound|apply octet_token_complete]. Qed.

Lemma expect_character text cursor character : forall next,
  expect text cursor character = Ready tt next <->
  String.get cursor text = Some character /\ next = S cursor.
Proof.
  intro next. unfold expect. destruct (String.get cursor text) as [actual|] eqn:Get.
  - destruct (Ascii.eqb actual character) eqn:Same.
    + apply Ascii.eqb_eq in Same. subst actual. split; intro Read;
        [injection Read as <-; auto|destruct Read as [_ ->]; reflexivity].
    + apply Ascii.eqb_neq in Same. split; [discriminate|]. intros [Equal _].
      injection Equal as Equal. contradiction.
  - split; [discriminate|]. intros [Impossible _]. discriminate.
Qed.

Lemma checked_quad_geometry a b c d cursor ip final :
  checked_quad a b c d cursor = Ready ip final ->
  0 <= a <= 255 /\ 0 <= b <= 255 /\ 0 <= c <= 255 /\ 0 <= d <= 255 /\
  value ip = ((a * 256 + b) * 256 + c) * 256 + d /\ final = cursor.
Proof.
  unfold checked_quad.
  repeat match goal with |- context[Z_le_dec ?left ?right] => destruct (Z_le_dec left right) end;
    intro Read; try discriminate.
  inversion Read; subst. cbn. repeat split; try reflexivity; lia.
Qed.

(** A dotted-quad grammar over byte positions and decimal values. Its
    components are not scanner transitions: they assert the full consumed
    byte spans, delimiters, no-octal spelling, numeric bounds and address
    polynomial. Arbitrarily long wrapped decimal strings remain explicit. *)
Definition quad_grammar text cursor final number :=
  exists a b c d first second third,
    octet_token text cursor first a /\ String.get first text = Some "."%char /\
    octet_token text (S first) second b /\ String.get second text = Some "."%char /\
    octet_token text (S second) third c /\ String.get third text = Some "."%char /\
    octet_token text (S third) final d /\
    0 <= a <= 255 /\ 0 <= b <= 255 /\ 0 <= c <= 255 /\ 0 <= d <= 255 /\
    number = ((a * 256 + b) * 256 + c) * 256 + d.

Theorem quad_success_grammar text cursor ip final :
  quad text cursor = Ready ip final -> quad_grammar text cursor final (value ip).
Proof.
  unfold quad, bind.
  destruct (octet text cursor) as [a first|reason] eqn:A; [|discriminate].
  destruct (expect text first "."%char) as [[] after_first|reason] eqn:Dot1; [|discriminate].
  apply expect_character in Dot1 as [Dot1 ->].
  destruct (octet text (S first)) as [b second|reason] eqn:B; [|discriminate].
  destruct (expect text second "."%char) as [[] after_second|reason] eqn:Dot2; [|discriminate].
  apply expect_character in Dot2 as [Dot2 ->].
  destruct (octet text (S second)) as [c third|reason] eqn:C; [|discriminate].
  destruct (expect text third "."%char) as [[] after_third|reason] eqn:Dot3; [|discriminate].
  apply expect_character in Dot3 as [Dot3 ->].
  destruct (octet text (S third)) as [d ending|reason] eqn:D; [|discriminate].
  intro Read. apply checked_quad_geometry in Read.
  destruct Read as [Ra [Rb [Rc [Rd [Value ->]]]]].
  apply octet_token_sound in A, B, C, D.
  exists a, b, c, d, first, second, third. repeat (first [assumption | split]).
Qed.

Lemma checked_quad_accepts a b c d cursor :
  0 <= a <= 255 -> 0 <= b <= 255 -> 0 <= c <= 255 -> 0 <= d <= 255 ->
  exists ip, checked_quad a b c d cursor = Ready ip cursor /\
    value ip = ((a * 256 + b) * 256 + c) * 256 + d.
Proof.
  intros Ra Rb Rc Rd. unfold checked_quad.
  repeat match goal with |- context[Z_le_dec ?left ?right] => destruct (Z_le_dec left right) end;
    try lia.
  eexists. split; reflexivity.
Qed.

Theorem quad_grammar_accepted text cursor final number :
  quad_grammar text cursor final number ->
  exists ip, quad text cursor = Ready ip final /\ value ip = number.
Proof.
  intros [a [b [c [d [first [second [third
    [A [Dot1 [B [Dot2 [C [Dot3 [D [Ra [Rb [Rc [Rd Value]]]]]]]]]]]]]]]]]].
  apply octet_token_complete in A, B, C, D.
  assert (expect text first "."%char = Ready tt (S first)) as Expect1
    by (apply expect_character; auto).
  assert (expect text second "."%char = Ready tt (S second)) as Expect2
    by (apply expect_character; auto).
  assert (expect text third "."%char = Ready tt (S third)) as Expect3
    by (apply expect_character; auto).
  unfold quad, bind. rewrite A, Expect1, B, Expect2, C, Expect3, D.
  destruct (@checked_quad_accepts a b c d final Ra Rb Rc Rd) as [ip [Read Geometry]].
  exists ip. split; [exact Read|congruence].
Qed.

Theorem of_string_success_grammar text ip final :
  of_string text = Ready ip final ->
  final = String.length text /\ quad_grammar text 0%nat final (value ip).
Proof.
  unfold of_string, finish, bind. destruct (quad text 0) as [parsed ending|reason] eqn:Read;
    [|discriminate].
  destruct (String.get ending text) as [character|] eqn:End; [discriminate|].
  intro Accepted. inversion Accepted; subst. apply quad_success_grammar in Read.
  split; [|exact Read]. apply text_get_none_iff in End.
  destruct Read as (a & b & c & d & first & second & third & _ & _ & _ & _ & _ & _ & D & _).
  destruct D as [[Bounds _] _].
  lia.
Qed.

Theorem of_string_grammar_accepted text number :
  quad_grammar text 0%nat (String.length text) number ->
  exists ip, of_string text = Ready ip (String.length text) /\ value ip = number.
Proof.
  intro Grammar. apply quad_grammar_accepted in Grammar as [ip [Read Geometry]].
  exists ip. split; [|exact Geometry]. unfold of_string, finish, bind. rewrite Read.
  assert (String.get (String.length text) text = None) as End by (apply text_get_none_iff; lia).
  now rewrite End.
Qed.

Lemma checked_prefix_geometry ip width cursor parsed final :
  checked_prefix ip width cursor = Ready parsed final ->
  network parsed = ip /\ Z.of_nat (bits parsed) = width /\ 0 <= width <= 32 /\ final = cursor.
Proof.
  unfold checked_prefix.
  repeat match goal with |- context[Z_le_dec ?left ?right] => destruct (Z_le_dec left right) end;
    intro Read; try discriminate.
  inversion Read; subst. cbn. rewrite Z2Nat.id by assumption.
  repeat split; try reflexivity; lia.
Qed.

Definition prefix_grammar text cursor final number width :=
  exists address_end, quad_grammar text cursor address_end number /\
    String.get address_end text = Some "/"%char /\
    decimal_token text (S address_end) final width /\ 0 <= width <= 32.

Theorem prefix_read_success_grammar text cursor parsed final :
  prefix_read text cursor = Ready parsed final ->
  prefix_grammar text cursor final (value (network parsed)) (Z.of_nat (bits parsed)).
Proof.
  unfold prefix_read, bind.
  destruct (quad text cursor) as [ip address_end|reason] eqn:Quad; [|discriminate].
  destruct (expect text address_end "/"%char) as [[] after_slash|reason] eqn:Slash; [|discriminate].
  apply expect_character in Slash as [Slash ->].
  destruct (decimal text (S address_end)) as [width ending|reason] eqn:Width; [|discriminate].
  intro Read. apply checked_prefix_geometry in Read as [Network [Bits [Range End]]].
  rewrite Network, Bits, End. exists address_end.
  split; [now apply quad_success_grammar|].
  split; [exact Slash|]. split; [now apply decimal_token_sound|exact Range].
Qed.

Lemma checked_prefix_accepts ip width cursor :
  0 <= width <= 32 ->
  exists parsed, checked_prefix ip width cursor = Ready parsed cursor /\
    network parsed = ip /\ Z.of_nat (bits parsed) = width.
Proof.
  intro Range. unfold checked_prefix.
  repeat match goal with |- context[Z_le_dec ?left ?right] => destruct (Z_le_dec left right) end;
    try lia.
  eexists. repeat split; try reflexivity. cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Theorem prefix_grammar_accepted text cursor final number width :
  prefix_grammar text cursor final number width ->
  exists parsed, prefix_read text cursor = Ready parsed final /\
    value (network parsed) = number /\ Z.of_nat (bits parsed) = width.
Proof.
  intros (address_end & Quad & Slash & Width & Range).
  apply quad_grammar_accepted in Quad as [ip [Quad Value]].
  apply decimal_token_complete in Width.
  assert (expect text address_end "/"%char = Ready tt (S address_end)) as Expect
    by (apply expect_character; auto).
  unfold prefix_read, bind. rewrite Quad, Expect, Width.
  destruct (@checked_prefix_accepts ip width final Range) as [parsed [Read [Network Bits]]].
  exists parsed. split; [exact Read|]. split; [now rewrite Network|exact Bits].
Qed.

Theorem prefix_of_string_success_grammar text parsed final :
  prefix_of_string text = Ready parsed final ->
  final = String.length text /\
  prefix_grammar text 0%nat final (value (network parsed)) (Z.of_nat (bits parsed)).
Proof.
  unfold prefix_of_string, finish, bind.
  destruct (prefix_read text 0) as [p ending|reason] eqn:Read; [|discriminate].
  destruct (String.get ending text) as [character|] eqn:End; [discriminate|].
  intro Accepted. inversion Accepted; subst. apply prefix_read_success_grammar in Read.
  split; [|exact Read]. apply text_get_none_iff in End.
  destruct Read as (address_end & _ & _ & [Bounds _] & _). lia.
Qed.

Theorem prefix_of_string_grammar_accepted text number width :
  prefix_grammar text 0%nat (String.length text) number width ->
  exists parsed, prefix_of_string text = Ready parsed (String.length text) /\
    value (network parsed) = number /\ Z.of_nat (bits parsed) = width.
Proof.
  intro Grammar. apply prefix_grammar_accepted in Grammar as [parsed [Read [Value Bits]]].
  exists parsed. split; [|auto]. unfold prefix_of_string, finish, bind. rewrite Read.
  assert (String.get (String.length text) text = None) as End by (apply text_get_none_iff; lia).
  now rewrite End.
Qed.

Definition address_language text number :=
  quad_grammar text 0%nat (String.length text) number.
Definition prefix_language text number width :=
  prefix_grammar text 0%nat (String.length text) number width.

Theorem address_language_iff text number :
  address_language text number <->
  exists ip final, of_string text = Ready ip final /\ value ip = number.
Proof.
  split.
  - intro Grammar. apply of_string_grammar_accepted in Grammar as [ip [Read Value]]. eauto.
  - intros (ip & final & Read & <-).
    apply of_string_success_grammar in Read as [-> Grammar]. exact Grammar.
Qed.

Theorem prefix_language_iff text number width :
  prefix_language text number width <->
  exists parsed final, prefix_of_string text = Ready parsed final /\
    value (network parsed) = number /\ Z.of_nat (bits parsed) = width.
Proof.
  split.
  - intro Grammar. apply prefix_of_string_grammar_accepted in Grammar as [p [Read [Value Bits]]]. eauto.
  - intros (p & final & Read & <- & <-).
    apply prefix_of_string_success_grammar in Read as [-> Grammar]. exact Grammar.
Qed.

Theorem address_rejected_iff text :
  (exists reason, of_string text = Failed reason) <->
  (forall number, ~ address_language text number).
Proof.
  split.
  - intros [reason Rejected] number Grammar.
    apply address_language_iff in Grammar as (ip & final & Read & _). congruence.
  - intro No_grammar. destruct (of_string text) as [ip final|reason] eqn:Read; [|eauto].
    exfalso. apply (No_grammar (value ip)). apply address_language_iff. eauto.
Qed.

Theorem prefix_rejected_iff text :
  (exists reason, prefix_of_string text = Failed reason) <->
  (forall number width, ~ prefix_language text number width).
Proof.
  split.
  - intros [reason Rejected] number width Grammar.
    apply prefix_language_iff in Grammar as (p & final & Read & _). congruence.
  - intro No_grammar. destruct (prefix_of_string text) as [p final|reason] eqn:Read; [|eauto].
    exfalso. apply (No_grammar (value (network p)) (Z.of_nat (bits p))).
    apply prefix_language_iff. eauto.
Qed.
