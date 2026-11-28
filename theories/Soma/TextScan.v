(** Source-defined byte-string scans. Counters descend from the actual input
    length; there is no independent fuel/input cap or whole-string byte list.
    The shared native extractor already lowers length/get/substring directly.
    Splitting walks backwards, retaining leading/trailing/consecutive empty
    fields and producing each segment once, as Stdlib.split_on_char does. *)
From Stdlib Require Import Strings.String Strings.Ascii List Bool Arith.PeanoNat Lia.
From Soma Require Import NativeText Strings.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.

Fixpoint contains_walk (text : string) (needle : ascii) (cursor remaining : nat) : bool :=
  match remaining with
  | 0 => false
  | S rest => match String.get cursor text with
    | None => false
    | Some character => if Ascii.eqb character needle then true
        else contains_walk text needle (S cursor) rest
    end
  end.

Fixpoint split_walk (separator : ascii) (text : string) (remaining finish : nat)
    (after : list string) : list string :=
  match remaining with
  | 0 => String.substring 0 finish text :: after
  | S index => match String.get index text with
    | Some character => if Ascii.eqb character separator then
        split_walk separator text index index
          (String.substring (S index) (finish - S index) text :: after)
      else split_walk separator text index finish after
    | None => split_walk separator text index finish after
    end
  end.

Fixpoint checked_contains_walk (text : string) (needle : ascii) (remaining : nat) :
    forall cursor, cursor + remaining <= String.length text -> bool :=
  match remaining as count return forall cursor, cursor + count <= String.length text -> bool with
  | 0 => fun _ _ => false
  | S rest => fun cursor Bound =>
      if Ascii.eqb (@Native.checked_byte text cursor ltac:(lia)) needle then true
      else @checked_contains_walk text needle rest (S cursor) ltac:(lia)
  end.

Fixpoint checked_split_walk (separator : ascii) (text : string) (remaining : nat) :
    forall finish, remaining <= finish -> finish <= String.length text -> list string -> list string :=
  match remaining as count return
      forall finish, count <= finish -> finish <= String.length text -> list string -> list string with
  | 0 => fun finish Order Bound after =>
      @Native.checked_substring text 0 finish ltac:(lia) :: after
  | S index => fun finish Order Bound after =>
      if Ascii.eqb (@Native.checked_byte text index ltac:(lia)) separator then
        @checked_split_walk separator text index index ltac:(lia) ltac:(lia)
          (@Native.checked_substring text (S index) (finish - S index) ltac:(lia) :: after)
      else @checked_split_walk separator text index finish ltac:(lia) Bound after
  end.

Theorem checked_contains_walk_agrees text needle remaining : forall cursor Bound,
  @checked_contains_walk text needle remaining cursor Bound = contains_walk text needle cursor remaining.
Proof.
  induction remaining as [|remaining IH]; intros cursor Bound; [reflexivity|].
  cbn [checked_contains_walk contains_walk]. unfold Native.checked_byte.
  destruct (text_get_defined text (index:=cursor) ltac:(lia)) as [character Read].
  rewrite Read. destruct (Ascii.eqb character needle); [reflexivity|apply IH].
Qed.

Theorem checked_split_walk_agrees separator text remaining : forall finish Order Bound after,
  @checked_split_walk separator text remaining finish Order Bound after = split_walk separator text remaining finish after.
Proof.
  induction remaining as [|index IH]; intros finish Order Bound after; [reflexivity|].
  cbn [checked_split_walk split_walk]. unfold Native.checked_byte, Native.checked_substring.
  destruct (text_get_defined text (index:=index) ltac:(lia)) as [character Read].
  rewrite Read. destruct (Ascii.eqb character separator); apply IH.
Qed.

Definition contains text needle := @checked_contains_walk text needle (String.length text) 0 ltac:(lia).
Definition split_on_char separator text :=
  @checked_split_walk separator text (String.length text) (String.length text) ltac:(lia) ltac:(lia) [].

Fixpoint join (separator : ascii) (parts : list string) : string :=
  match parts with
  | [] => EmptyString
  | [part] => part
  | part :: rest => String.append part (String separator (join separator rest))
  end.
Definition excludes (separator : ascii) (text : string) :=
  forall index, String.get index text <> Some separator.

Theorem contains_cursors_fit text cursor remaining :
  NativeSemantics.text_fits text -> cursor + remaining <= String.length text ->
  NativeWord.nat_fits cursor /\ NativeWord.nat_fits remaining /\
  (0 < remaining -> NativeWord.nat_fits (S cursor)).
Proof.
  intros Fits Bound. split; [|split].
  - apply text_index_fits_carrier with (text:=text); [exact Fits|lia].
  - apply text_index_fits_carrier with (text:=text); [exact Fits|lia].
  - intro Positive. apply text_index_fits_carrier with (text:=text); [exact Fits|lia].
Qed.

Theorem split_cursors_fit text remaining finish :
  NativeSemantics.text_fits text -> remaining <= finish -> finish <= String.length text ->
  NativeWord.nat_fits remaining /\ NativeWord.nat_fits finish /\ NativeWord.nat_fits (finish - remaining).
Proof.
  intros Fits Order Bound. repeat split;
    apply text_index_fits_carrier with (text:=text); [exact Fits|lia|exact Fits|lia|exact Fits|lia].
Qed.

Theorem contains_walk_correct text needle remaining : forall cursor,
  cursor + remaining <= String.length text ->
  (contains_walk text needle cursor remaining = true <->
   exists index, cursor <= index /\ index < cursor + remaining /\ String.get index text = Some needle).
Proof.
  induction remaining as [|remaining IH]; intros cursor Bound; cbn [contains_walk].
  - split; [discriminate|intros [index [Low [High _]]]; lia].
  - destruct (text_get_defined text (index:=cursor) ltac:(lia)) as [character Read].
    rewrite Read. destruct (Ascii.eqb character needle) eqn:Same.
    + apply Ascii.eqb_eq in Same. subst character. split; intros _.
      * exists cursor. repeat split; auto; lia.
      * reflexivity.
    + rewrite IH by lia. apply Ascii.eqb_neq in Same. split.
      * intros [index [Low [High Byte]]]. exists index. repeat split; auto; lia.
      * intros [index [Low [High Byte]]]. exists index. repeat split; auto; try lia.
        destruct (Nat.eq_dec index cursor); subst; [congruence|lia].
Qed.

Theorem contains_correct text needle :
  contains text needle = true <-> exists index, String.get index text = Some needle.
Proof.
  unfold contains. rewrite checked_contains_walk_agrees, contains_walk_correct by lia. split.
  - intros [index [_ [_ Read]]]. eauto.
  - intros [index Read]. exists index. repeat split; try lia; [|exact Read].
    assert (forall text index character, String.get index text = Some character -> index < String.length text) as InBounds.
    { intro source. induction source as [|head rest IH]; intros [|position] character Get;
        cbn in *; try discriminate; [lia|]. apply IH in Get. lia. }
    eauto.
Qed.

Theorem contains_false_excludes text needle : contains text needle = false <-> excludes needle text.
Proof.
  unfold excludes. split.
  - intros Absent index Read.
    assert (contains text needle = true) as Found by (apply contains_correct; eauto).
    congruence.
  - intros Absent. destruct (contains text needle) eqn:Found; [|reflexivity].
    apply contains_correct in Found. destruct Found as [index Read]. exfalso. exact (Absent index Read).
Qed.

Lemma prefix_at_byte text index finish separator :
  String.get index text = Some separator -> S index <= finish ->
  String.substring 0 finish text = String.append (String.substring 0 index text)
    (String separator (String.substring (S index) (finish - S index) text)).
Proof.
  revert index finish. induction text as [|character rest IH]; intros [|index] [|finish] Read Bound;
    cbn in *; try discriminate; try lia.
  - injection Read as Equal. subst character. now rewrite Nat.sub_0_r.
  - f_equal. apply IH; [exact Read|lia].
Qed.

Lemma join_split_head separator prefix suffix after :
  join separator (prefix :: suffix :: after) =
  join separator (String.append prefix (String separator suffix) :: after).
Proof.
  destruct after as [|head rest]; cbn [join]; [reflexivity|].
  rewrite Strings.append_assoc. reflexivity.
Qed.

Theorem split_walk_reassembles separator text remaining : forall finish after,
  remaining <= finish -> finish <= String.length text ->
  join separator (split_walk separator text remaining finish after) =
  join separator (String.substring 0 finish text :: after).
Proof.
  induction remaining as [|index IH]; intros finish after Order Bound; [reflexivity|].
  cbn [split_walk]. destruct (text_get_defined text (index:=index) ltac:(lia)) as [character Read].
  rewrite Read. destruct (Ascii.eqb character separator) eqn:Same.
  - apply Ascii.eqb_eq in Same. subst character. rewrite IH by lia.
    rewrite join_split_head. now rewrite <- (@prefix_at_byte text index finish separator Read Order).
  - apply IH; lia.
Qed.

Lemma prefix_whole text : String.substring 0 (String.length text) text = text.
Proof. induction text; cbn; [reflexivity|now rewrite IHtext]. Qed.

Theorem split_reassembles separator text : join separator (split_on_char separator text) = text.
Proof.
  unfold split_on_char. rewrite checked_split_walk_agrees, split_walk_reassembles by lia.
  cbn [join]. apply prefix_whole.
Qed.

Lemma slice_excludes separator text start size :
  (forall index, start <= index -> index < start + size -> String.get index text <> Some separator) ->
  excludes separator (String.substring start size text).
Proof.
  intros Absent index Read. destruct (Nat.lt_ge_cases index size).
  - rewrite String.substring_correct1 in Read by assumption.
    eapply (Absent (index + start)); [lia|lia|exact Read].
  - rewrite String.substring_correct2 in Read by assumption. discriminate.
Qed.

Theorem split_walk_excludes separator text remaining : forall finish after,
  remaining <= finish -> finish <= String.length text ->
  (forall index, remaining <= index -> index < finish -> String.get index text <> Some separator) ->
  Forall (excludes separator) after ->
  Forall (excludes separator) (split_walk separator text remaining finish after).
Proof.
  induction remaining as [|index IH]; intros finish after Order Bound Gap After.
  - constructor; [apply slice_excludes; intros; apply Gap; lia|exact After].
  - cbn [split_walk]. destruct (text_get_defined text (index:=index) ltac:(lia)) as [character Read].
    rewrite Read. destruct (Ascii.eqb character separator) eqn:Same.
    + apply Ascii.eqb_eq in Same. subst character. apply IH; [lia|lia| |].
      * intros; lia.
      * constructor; [apply slice_excludes; intros; apply Gap; lia|exact After].
    + apply Ascii.eqb_neq in Same. apply IH; [lia|lia| |exact After].
      intros position Low High Byte. destruct (Nat.eq_dec position index); subst.
      * congruence.
      * eapply (Gap position); [lia|exact High|exact Byte].
Qed.

Theorem split_components_exclude_separator separator text :
  Forall (excludes separator) (split_on_char separator text).
Proof. unfold split_on_char. rewrite checked_split_walk_agrees. apply split_walk_excludes; try lia. constructor. Qed.

Theorem split_walk_nonempty separator text remaining : forall finish after,
  split_walk separator text remaining finish after <> [].
Proof.
  induction remaining as [|index IH]; intros finish after; [discriminate|].
  cbn [split_walk]. destruct (String.get index text) as [character|]; [destruct (Ascii.eqb character separator)|]; apply IH.
Qed.

Theorem split_nonempty separator text : split_on_char separator text <> [].
Proof. unfold split_on_char. rewrite checked_split_walk_agrees. apply split_walk_nonempty. Qed.
