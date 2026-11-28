(** Contracts for the owned native string primitives. String payloads model
    byte contents; physical string identity, GC and allocation failure remain
    separate refinement obligations. Nat indices require the extraction
    carrier's actual signed-int representability, not an application cap. *)
From Soma Require Import Native NativeSemantics NativeTotal.
From Soma Require NativeWord.
From Stdlib Require Import Strings.String ZArith Lia.
Set Implicit Arguments.

Theorem text_index_fits_carrier text index :
  text_fits text -> index <= String.length text -> NativeWord.nat_fits index.
Proof.
  unfold text_fits, NativeWord.string_limit, NativeWord.nat_fits.
  intros Fits Bound. apply Nat2Z.inj_le in Bound. lia.
Qed.

Theorem text_get_defined text index :
  index < String.length text -> exists character, String.get index text = Some character.
Proof.
  revert index. induction text as [|character rest IH]; intros [|index] Bound; cbn in *; try lia; eauto.
  apply IH. lia.
Qed.

Theorem text_slice_length text start size :
  start + size <= String.length text -> String.length (String.substring start size text) = size.
Proof.
  revert start size. induction text as [|character rest IH]; intros [|start] [|size] Bound;
    cbn in *; try lia; try (apply IH; lia).
  f_equal. apply IH. lia.
Qed.

Theorem checked_byte_correct text index Bound :
  String.get index text = Some (@Native.checked_byte text index Bound).
Proof.
  unfold Native.checked_byte.
  destruct (text_get_defined text Bound) as [character Read]. now rewrite Read.
Qed.

Theorem checked_substring_length text start size Bound :
  String.length (@Native.checked_substring text start size Bound) = size.
Proof. now apply text_slice_length. Qed.

Section Text.
Variable foreign : forall A : Type, (unit -> A) -> world -> result A -> world -> Prop.
Variable named : forall A B : Type, string -> string -> A -> world -> result B -> world -> Prop.

Definition string_successor {A} w (body : Native.program A) w' (following : Native.program A) :=
  (match body in Native.program T return Native.program T -> Prop with
  | Native.String_length text => fun last => text_fits text /\ w' = w /\
      last = Native.Return (NativeWord.of_nat (String.length text))
  | Native.String_get text index => fun last => text_fits text /\
      match NativeWord.bounded_index index (String.length text) with
      | Some position => exists character, String.get position text = Some character /\
          w' = w /\ last = Native.Return character
      | None => w' = bounds_world w /\ last = Native.Throw (bounds_value w)
      end
  | Native.String_get_nat text index => fun last => text_fits text /\ NativeWord.nat_fits index /\
      match String.get index text with
      | Some character => w' = w /\ last = Native.Return character
      | None => w' = bounds_world w /\ last = Native.Throw (bounds_value w)
      end
  | Native.String_substring text offset count => fun last => text_fits text /\
      match NativeWord.bounded_slice offset count (String.length text) with
      | Some (start, size) => w' = w /\ last = Native.Return (String.substring start size text)
      | None => w' = with_fault w (Fault_invalid_argument "String.sub / Bytes.sub") /\
          last = Native.Throw (fault_handle w)
      end
  | _ => fun _ => True
  end) following.

Theorem step_string_successor A w (body : Native.program A) w' following :
  step foreign named w body w' following -> string_successor w body w' following.
Proof.
  intro Move. destruct Move; cbn [string_successor]; try exact I.
  all: repeat match goal with
    | H : NativeWord.bounded_index _ _ = _ |- context[NativeWord.bounded_index _ _] => rewrite H
    | H : NativeWord.bounded_slice _ _ _ = _ |- context[NativeWord.bounded_slice _ _ _] => rewrite H
    | H : String.get _ _ = _ |- context[String.get _ _] => rewrite H
    end; eauto 8.
Qed.

Theorem string_length_total post w text :
  text_fits text -> post w (Returned (NativeWord.of_nat (String.length text))) ->
  total foreign named post (w, Native.String_length text).
Proof.
  intros Fits Post. apply successors_give_total.
  - exists (w, Native.Return (NativeWord.of_nat (String.length text))).
    unfold transition; cbn. now apply Step_string_length.
  - intros [final following] Move. unfold transition in Move; cbn in Move.
    apply step_string_successor in Move. cbn [string_successor] in Move.
    destruct Move as [_ [World Equal]]. subst. now apply return_is_total.
Qed.

Theorem string_get_total post w text index position character :
  text_fits text -> NativeWord.bounded_index index (String.length text) = Some position ->
  String.get position text = Some character -> post w (Returned character) ->
  total foreign named post (w, Native.String_get text index).
Proof.
  intros Fits Index Character Post. apply successors_give_total.
  - exists (w, Native.Return character). unfold transition; cbn. eapply Step_string_get; eassumption.
  - intros [final following] Move. unfold transition in Move; cbn in Move.
    apply step_string_successor in Move. cbn [string_successor] in Move. rewrite Index in Move.
    destruct Move as [_ [observed [Read [World Equal]]]]. rewrite Character in Read.
    injection Read as Same. subst. now apply return_is_total.
Qed.

Theorem string_get_invalid_total post w text index :
  text_fits text -> NativeWord.bounded_index index (String.length text) = None ->
  post (bounds_world w) (Raised (bounds_value w)) ->
  total foreign named post (w, Native.String_get text index).
Proof.
  intros Fits Index Post. apply successors_give_total.
  - exists (bounds_world w, Native.Throw (bounds_value w)). unfold transition; cbn.
    now apply Step_string_get_invalid.
  - intros [final following] Move. unfold transition in Move; cbn in Move.
    apply step_string_successor in Move. cbn [string_successor] in Move. rewrite Index in Move.
    destruct Move as [_ [World Equal]]. subst. now apply throw_is_total.
Qed.

Theorem string_get_nat_total post w text index character :
  text_fits text -> NativeWord.nat_fits index -> String.get index text = Some character ->
  post w (Returned character) -> total foreign named post (w, Native.String_get_nat text index).
Proof.
  intros Fits Index Character Post. apply successors_give_total.
  - exists (w, Native.Return character). unfold transition; cbn. eapply Step_string_get_nat; eassumption.
  - intros [final following] Move. unfold transition in Move; cbn in Move.
    apply step_string_successor in Move. cbn [string_successor] in Move. rewrite Character in Move.
    destruct Move as [_ [_ [World Equal]]]. subst. now apply return_is_total.
Qed.

Theorem string_get_nat_invalid_total post w text index :
  text_fits text -> NativeWord.nat_fits index -> String.get index text = None ->
  post (bounds_world w) (Raised (bounds_value w)) ->
  total foreign named post (w, Native.String_get_nat text index).
Proof.
  intros Fits Index Character Post. apply successors_give_total.
  - exists (bounds_world w, Native.Throw (bounds_value w)). unfold transition; cbn.
    eapply Step_string_get_nat_invalid; eassumption.
  - intros [final following] Move. unfold transition in Move; cbn in Move.
    apply step_string_successor in Move. cbn [string_successor] in Move. rewrite Character in Move.
    destruct Move as [_ [_ [World Equal]]]. subst. now apply throw_is_total.
Qed.

Theorem string_substring_total post w text offset count start size :
  text_fits text -> NativeWord.bounded_slice offset count (String.length text) = Some (start, size) ->
  post w (Returned (String.substring start size text)) ->
  total foreign named post (w, Native.String_substring text offset count).
Proof.
  intros Fits Span Post. apply successors_give_total.
  - exists (w, Native.Return (String.substring start size text)). unfold transition; cbn.
    now apply Step_string_substring.
  - intros [final following] Move. unfold transition in Move; cbn in Move.
    apply step_string_successor in Move. cbn [string_successor] in Move. rewrite Span in Move.
    destruct Move as [_ [World Equal]]. subst. now apply return_is_total.
Qed.

Theorem string_substring_invalid_total post w text offset count :
  text_fits text -> NativeWord.bounded_slice offset count (String.length text) = None ->
  post (with_fault w (Fault_invalid_argument "String.sub / Bytes.sub")) (Raised (fault_handle w)) ->
  total foreign named post (w, Native.String_substring text offset count).
Proof.
  intros Fits Span Post. apply successors_give_total.
  - exists (with_fault w (Fault_invalid_argument "String.sub / Bytes.sub"), Native.Throw (fault_handle w)).
    unfold transition; cbn. now apply Step_string_substring_invalid.
  - intros [final following] Move. unfold transition in Move; cbn in Move.
    apply step_string_successor in Move. cbn [string_successor] in Move. rewrite Span in Move.
    destruct Move as [_ [World Equal]]. subst. now apply throw_is_total.
Qed.
End Text.
