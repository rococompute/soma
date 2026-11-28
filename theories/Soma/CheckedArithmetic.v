(** Binary integer arithmetic checked before conversion to the native signed
    63-bit carrier. These are numeric Source contracts, not assumptions about
    wrapping PrimInt63 operations. The compiler/word conversion refinement is
    a separate obligation. The bound is the actual 64-bit OCaml int profile,
    not a guest input/fuel limit. *)
From Stdlib Require Import ZArith Lia Bool.
Local Open Scope Z_scope.
Set Implicit Arguments.

Definition minimum : Z := -(2 ^ 62).
Definition maximum : Z := 2 ^ 62 - 1.
Definition fits number := minimum <= number <= maximum.
Definition fitsb number := Z.leb minimum number && Z.leb number maximum.
Definition checked number := if fitsb number then Some number else None.
Definition add left right := checked (left + right).
Definition sub left right := checked (left - right).
Definition mul left right := checked (left * right).

Theorem fitsb_spec number : fitsb number = true <-> fits number.
Proof. unfold fitsb, fits. rewrite andb_true_iff, !Z.leb_le. tauto. Qed.

Theorem checked_spec number result : checked number = Some result <-> result = number /\ fits number.
Proof.
  unfold checked. destruct (fitsb number) eqn:Fit.
  - apply fitsb_spec in Fit. split; intro Same; [injection Same as <-; auto|destruct Same as [-> _]; reflexivity].
  - split; [discriminate|]. intros [_ Inside]. apply fitsb_spec in Inside. congruence.
Qed.

Theorem checked_rejects number : checked number = None <-> ~ fits number.
Proof.
  unfold checked. destruct (fitsb number) eqn:Fit.
  - apply fitsb_spec in Fit. split; [discriminate|tauto].
  - split; [|reflexivity]. intros _ Inside. apply fitsb_spec in Inside. congruence.
Qed.

Theorem add_spec left right result : add left right = Some result <-> result = left + right /\ fits (left + right).
Proof. apply checked_spec. Qed.
Theorem sub_spec left right result : sub left right = Some result <-> result = left - right /\ fits (left - right).
Proof. apply checked_spec. Qed.
Theorem mul_spec left right result : mul left right = Some result <-> result = left * right /\ fits (left * right).
Proof. apply checked_spec. Qed.

Definition span_valid beginning count := 0 <= beginning /\ 0 <= count /\ beginning + count <= maximum.
Record span := Span {
  beginning : Z; ending : Z;
  ordered : 0 <= beginning <= ending;
  representable : ending <= maximum
}.
Definition length range := ending range - beginning range.

Definition checked_span (start count : Z) : option span.
Proof.
  destruct (Z_le_dec 0 start) as [Start|Invalid]; [|exact None].
  destruct (Z_le_dec 0 count) as [Count|Invalid]; [|exact None].
  destruct (Z_le_dec (start + count) maximum) as [End|Invalid]; [|exact None].
  exact (Some (@Span start (start + count) ltac:(lia) End)).
Defined.

Theorem checked_span_sound start count range :
  checked_span start count = Some range ->
  beginning range = start /\ ending range = start + count /\ span_valid start count.
Proof.
  unfold checked_span. repeat match goal with |- context[Z_le_dec ?a ?b] => destruct (Z_le_dec a b) end;
    intro Read; try discriminate.
  inversion Read; subst. cbn. unfold span_valid. repeat split; try reflexivity; lia.
Qed.

Theorem checked_span_complete start count : span_valid start count ->
  exists range, checked_span start count = Some range /\ beginning range = start /\ length range = count.
Proof.
  intros [Start [Count End]]. unfold checked_span.
  repeat match goal with |- context[Z_le_dec ?a ?b] => destruct (Z_le_dec a b) end; try lia.
  eexists. split; [reflexivity|]. split; [reflexivity|].
  unfold length. cbn [beginning ending]. lia.
Qed.

Theorem checked_span_rejects start count :
  checked_span start count = None <-> ~ span_valid start count.
Proof.
  split.
  - intros Read Valid. apply checked_span_complete in Valid as [range [Accepted _]]. congruence.
  - intro Invalid. destruct (checked_span start count) as [range|] eqn:Read; [|reflexivity].
    exfalso. apply Invalid. now apply checked_span_sound in Read as [_ [_ Valid]].
Qed.

Theorem span_length_bounds range : 0 <= length range <= maximum.
Proof. unfold length. pose proof (ordered range). pose proof (representable range). lia. Qed.

Theorem span_cursor_fits range cursor : beginning range <= cursor <= ending range -> fits cursor.
Proof.
  intros Bounds. pose proof (ordered range). pose proof (representable range).
  unfold fits, minimum, maximum in *. lia.
Qed.

Theorem span_slice_bounds range first last :
  beginning range <= first <= last -> last <= ending range ->
  0 <= first - beginning range /\ 0 <= last - first /\
  (first - beginning range) + (last - first) <= length range.
Proof. unfold length. intros. lia. Qed.

Definition checked_scale_end start count stride :=
  if Z.leb 0 count && Z.leb 0 stride then checked_span start (count * stride) else None.

Theorem checked_scale_end_sound start count stride range :
  checked_scale_end start count stride = Some range ->
  0 <= count /\ 0 <= stride /\ beginning range = start /\ ending range = start + count * stride /\
  span_valid start (count * stride).
Proof.
  unfold checked_scale_end. destruct (Z.leb 0 count && Z.leb 0 stride) eqn:Nonnegative; [|discriminate].
  apply andb_true_iff in Nonnegative as [Count Stride]. apply Z.leb_le in Count, Stride.
  intro Read. apply checked_span_sound in Read. tauto.
Qed.

Theorem checked_scale_end_complete start count stride :
  0 <= count -> 0 <= stride -> span_valid start (count * stride) ->
  exists range, checked_scale_end start count stride = Some range /\ length range = count * stride.
Proof.
  intros Count Stride Valid. unfold checked_scale_end.
  rewrite (proj2 (Z.leb_le 0 count) Count), (proj2 (Z.leb_le 0 stride) Stride). cbn.
  apply checked_span_complete in Valid as [range [Read [_ Length]]]. eauto.
Qed.

Theorem overflow_span_rejected start count : maximum < start + count -> checked_span start count = None.
Proof. intro Overflow. apply checked_span_rejects. unfold span_valid. lia. Qed.

Theorem signed_add_overflow_rejected : add maximum 1 = None.
Proof. apply checked_rejects. unfold fits, maximum. lia. Qed.
