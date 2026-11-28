(** Checked binary arithmetic at the actual signed 63-bit boundary.

    The round-trip and non-wrapping refinement results use the existing Rocq
    primitive specifications in Uint63Axioms/Sint63Axioms. Those are explicit
    trusted laws, not new axioms or proofs of the OCaml extraction/runtime.
    The contract fixture inventories each theorem's complete assumption set.
    All guards operate on binary integers before encoding a native word. *)
From Soma Require Import NativeWord CheckedArithmetic.
From Stdlib Require Import Sint63 ZArith Lia Bool.
Local Open Scope Z_scope.

Definition encode := Uint63Axioms.of_Z.

Theorem decode_bounds value : CheckedArithmetic.fits (NativeWord.signed value).
Proof.
  pose proof (Sint63.to_Z_bounded value) as Bound.
  change (CheckedArithmetic.fits (NativeWord.signed value)) in Bound. exact Bound.
Qed.

Theorem decode_encode value : CheckedArithmetic.fits value ->
  NativeWord.signed (encode value) = value.
Proof. intro Bound. symmetry. apply Sint63.is_int. exact Bound. Qed.

Theorem encode_decode value : encode (NativeWord.signed value) = value.
Proof. apply Sint63.of_to_Z. Qed.

Theorem decode_injective left right : NativeWord.signed left = NativeWord.signed right -> left = right.
Proof. intro Same. rewrite <- (encode_decode left), <- (encode_decode right). now rewrite Same. Qed.

Theorem decode_add left right :
  CheckedArithmetic.fits (NativeWord.signed left + NativeWord.signed right) ->
  NativeWord.signed (PrimInt63.add left right) = NativeWord.signed left + NativeWord.signed right.
Proof. apply Sint63.to_Z_add. Qed.

Theorem decode_sub left right :
  CheckedArithmetic.fits (NativeWord.signed left - NativeWord.signed right) ->
  NativeWord.signed (PrimInt63.sub left right) = NativeWord.signed left - NativeWord.signed right.
Proof. apply Sint63.to_Z_sub. Qed.

Theorem decode_mul left right :
  CheckedArithmetic.fits (NativeWord.signed left * NativeWord.signed right) ->
  NativeWord.signed (PrimInt63.mul left right) = NativeWord.signed left * NativeWord.signed right.
Proof. apply Sint63.to_Z_mul. Qed.

Theorem signed_lt_spec left right : PrimInt63.ltsb left right = true <->
  NativeWord.signed left < NativeWord.signed right.
Proof. apply Sint63Axioms.ltb_spec. Qed.
Theorem signed_le_spec left right : PrimInt63.lesb left right = true <->
  NativeWord.signed left <= NativeWord.signed right.
Proof. apply Sint63Axioms.leb_spec. Qed.

Definition of_Z value := option_map encode (CheckedArithmetic.checked value).
Definition add left right := of_Z (NativeWord.signed left + NativeWord.signed right).
Definition sub left right := of_Z (NativeWord.signed left - NativeWord.signed right).
Definition mul left right := of_Z (NativeWord.signed left * NativeWord.signed right).

Theorem of_Z_spec value result : of_Z value = Some result <->
  NativeWord.signed result = value /\ CheckedArithmetic.fits value.
Proof.
  unfold of_Z. destruct (CheckedArithmetic.checked value) as [number|] eqn:Read; cbn.
  - apply CheckedArithmetic.checked_spec in Read as [-> Bound]. split.
    + intro Same. inversion Same; subst. split; [now apply decode_encode|exact Bound].
    + intros [Same _]. f_equal. apply decode_injective. now rewrite decode_encode by exact Bound.
  - split; [discriminate|]. intros [_ Bound]. apply CheckedArithmetic.checked_rejects in Read. tauto.
Qed.

Theorem of_Z_rejects value : of_Z value = None <-> ~ CheckedArithmetic.fits value.
Proof.
  unfold of_Z. destruct (CheckedArithmetic.checked value) as [number|] eqn:Read; cbn.
  - apply CheckedArithmetic.checked_spec in Read as [_ Bound]. split; [discriminate|tauto].
  - split; [|reflexivity]. intros _. now apply CheckedArithmetic.checked_rejects in Read.
Qed.

Theorem add_spec left right result : add left right = Some result <->
  NativeWord.signed result = NativeWord.signed left + NativeWord.signed right /\
  CheckedArithmetic.fits (NativeWord.signed left + NativeWord.signed right).
Proof. apply of_Z_spec. Qed.
Theorem sub_spec left right result : sub left right = Some result <->
  NativeWord.signed result = NativeWord.signed left - NativeWord.signed right /\
  CheckedArithmetic.fits (NativeWord.signed left - NativeWord.signed right).
Proof. apply of_Z_spec. Qed.
Theorem mul_spec left right result : mul left right = Some result <->
  NativeWord.signed result = NativeWord.signed left * NativeWord.signed right /\
  CheckedArithmetic.fits (NativeWord.signed left * NativeWord.signed right).
Proof. apply of_Z_spec. Qed.

Theorem add_native left right result : add left right = Some result -> result = PrimInt63.add left right.
Proof. intro Read. apply add_spec in Read as [Value Bound]. apply decode_injective. now rewrite decode_add. Qed.
Theorem sub_native left right result : sub left right = Some result -> result = PrimInt63.sub left right.
Proof. intro Read. apply sub_spec in Read as [Value Bound]. apply decode_injective. now rewrite decode_sub. Qed.
Theorem mul_native left right result : mul left right = Some result -> result = PrimInt63.mul left right.
Proof. intro Read. apply mul_spec in Read as [Value Bound]. apply decode_injective. now rewrite decode_mul. Qed.

(** Nonnegative pointer/count spans use the same checked mathematical endpoint
    as CheckedArithmetic. The count is binary and need not arrive as an already
    wrapped word. An unrepresentable exclusive endpoint is rejected. *)
Definition advance position count :=
  match CheckedArithmetic.checked_span (NativeWord.signed position) count with
  | Some range => Some (encode (CheckedArithmetic.ending range))
  | None => None
  end.

Theorem advance_spec position count result : advance position count = Some result <->
  CheckedArithmetic.span_valid (NativeWord.signed position) count /\
  NativeWord.signed result = NativeWord.signed position + count.
Proof.
  unfold advance. destruct (CheckedArithmetic.checked_span (NativeWord.signed position) count) as [range|] eqn:Read.
  - pose proof (@CheckedArithmetic.checked_span_sound _ _ _ Read) as [Start [End Valid]].
    assert (CheckedArithmetic.fits (CheckedArithmetic.ending range)) as Fits.
    { apply (CheckedArithmetic.span_cursor_fits range). pose proof (CheckedArithmetic.ordered range). lia. }
    split.
    + intro Same. inversion Same; subst. split; [exact Valid|]. now rewrite decode_encode by exact Fits.
    + intros [_ Value]. f_equal. apply decode_injective. rewrite decode_encode by exact Fits. congruence.
  - split; [discriminate|]. intros [Valid _]. apply CheckedArithmetic.checked_span_rejects in Read. tauto.
Qed.

Theorem advance_rejects position count : advance position count = None <->
  ~ CheckedArithmetic.span_valid (NativeWord.signed position) count.
Proof.
  unfold advance. destruct (CheckedArithmetic.checked_span (NativeWord.signed position) count) as [range|] eqn:Read.
  - apply CheckedArithmetic.checked_span_sound in Read as [_ [_ Valid]]. split; [discriminate|tauto].
  - split; [|reflexivity]. intros _. now apply CheckedArithmetic.checked_span_rejects in Read.
Qed.

Theorem advance_bounds position count result : advance position count = Some result ->
  0 <= NativeWord.signed position <= NativeWord.signed result /\
  NativeWord.signed result <= CheckedArithmetic.maximum /\
  NativeWord.signed result - NativeWord.signed position = count.
Proof. intro Read. apply advance_spec in Read as [[Start [Count End]] Value]. repeat split; lia. Qed.

Theorem advance_progress position count result : advance position count = Some result ->
  0 < count -> NativeWord.signed position < NativeWord.signed result.
Proof. intros Read Positive. apply advance_bounds in Read. lia. Qed.

Theorem advance_native position count result : advance position count = Some result ->
  result = PrimInt63.add position (encode count).
Proof.
  intro Read. apply advance_spec in Read as [[Start [Count End]] Value].
  assert (CheckedArithmetic.fits count) as CountFits by
    (unfold CheckedArithmetic.fits, CheckedArithmetic.minimum; lia).
  apply decode_injective. rewrite decode_add, decode_encode; try exact CountFits.
  - exact Value.
  - rewrite decode_encode by exact CountFits.
    unfold CheckedArithmetic.fits, CheckedArithmetic.minimum. lia.
Qed.

Definition scaled_advance position count stride :=
  if Z.leb 0 count && Z.leb 0 stride then advance position (count * stride) else None.

Theorem scaled_advance_spec position count stride result : scaled_advance position count stride = Some result <->
  0 <= count /\ 0 <= stride /\
  CheckedArithmetic.span_valid (NativeWord.signed position) (count * stride) /\
  NativeWord.signed result = NativeWord.signed position + count * stride.
Proof.
  unfold scaled_advance. destruct (Z.leb 0 count && Z.leb 0 stride) eqn:Nonnegative.
  - apply andb_true_iff in Nonnegative as [Count Stride]. apply Z.leb_le in Count, Stride.
    rewrite advance_spec. tauto.
  - split; [discriminate|]. intros [Count [Stride _]].
    assert (Z.leb 0 count && Z.leb 0 stride = true) as Accepted by
      (apply andb_true_iff; split; now apply Z.leb_le). congruence.
Qed.

Theorem scaled_advance_bounds position count stride result : scaled_advance position count stride = Some result ->
  0 <= NativeWord.signed position <= NativeWord.signed result /\
  NativeWord.signed result <= CheckedArithmetic.maximum /\
  NativeWord.signed result - NativeWord.signed position = count * stride.
Proof. intro Read. apply scaled_advance_spec in Read as [Count [Stride [[Start [Size End]] Value]]]. repeat split; lia. Qed.

Theorem scaled_advance_progress position count stride result : scaled_advance position count stride = Some result ->
  0 < count -> 0 < stride -> NativeWord.signed position < NativeWord.signed result.
Proof. intros Read Count Stride. apply scaled_advance_bounds in Read. nia. Qed.
