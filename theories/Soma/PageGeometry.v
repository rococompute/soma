(** Exact page/region boundaries and checked span progression in binary Z.
    Field observations are data in this model; no native page reply is
    declared correct by assumption. Mapping to a physical frame and the
    existing PrimInt63 traversal are separate refinement obligations. *)
From Soma Require CheckedArithmetic.
From Stdlib Require Import ZArith Lia List Bool.
Import ListNotations.
Local Open Scope Z_scope.
Set Implicit Arguments.

Definition page_size : Z := 4096.
Definition page_base address := (address / page_size) * page_size.
Definition page_end address := page_base address + page_size.
Definition page_offset address := address mod page_size.

Theorem page_interval address : page_base address <= address < page_end address.
Proof.
  unfold page_end, page_base, page_size.
  pose proof (Z.div_mod address 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound address 4096 ltac:(lia)). nia.
Qed.

Theorem page_offset_bounds address : 0 <= page_offset address < page_size.
Proof. unfold page_offset, page_size. apply Z.mod_pos_bound. lia. Qed.

Theorem page_decomposes address : address = page_base address + page_offset address.
Proof. unfold page_base, page_offset, page_size. pose proof (Z.div_mod address 4096 ltac:(lia)). nia. Qed.

Theorem page_end_aligned address : page_end address mod page_size = 0.
Proof.
  unfold page_end, page_base, page_size.
  replace (address / 4096 * 4096 + 4096) with ((address / 4096 + 1) * 4096) by lia.
  apply Z.mod_mul. lia.
Qed.

Theorem same_page_before_end address cursor :
  address <= cursor < page_end address -> cursor / page_size = address / page_size.
Proof.
  intro Bounds. pose proof (page_interval address).
  unfold page_end, page_base in *.
  symmetry. apply Z.div_unique with (r := cursor - page_size * (address / page_size));
    unfold page_size in *; nia.
Qed.

Record layout := Layout { low : Z; high : Z; cow_low : Z; cow_high : Z; high_base : Z }.
Definition paged window address :=
  Z.leb (high_base window) address || (Z.leb (cow_low window) address && Z.ltb address (cow_high window)).
Definition select_boundary address before candidate :=
  if Z.ltb address candidate && Z.ltb candidate before then candidate else before.
Definition boundaries window := [low window; high window; cow_low window; cow_high window].
Definition region_end window address := fold_left (select_boundary address) (boundaries window) (high_base window).
Definition run_end window address := if paged window address then page_end address else region_end window address.

Lemma selected_boundary_progress address before candidate : address < before -> address < select_boundary address before candidate.
Proof.
  intro Progress. unfold select_boundary.
  destruct (Z.ltb address candidate && Z.ltb candidate before) eqn:Selected; [|exact Progress].
  apply andb_true_iff in Selected as [Forward _]. now apply Z.ltb_lt.
Qed.

Lemma folded_boundary_progress address candidates : forall before,
  address < before -> address < fold_left (select_boundary address) candidates before.
Proof.
  induction candidates as [|candidate rest IH]; intros before Progress; cbn; [exact Progress|].
  apply IH. now apply selected_boundary_progress.
Qed.

Theorem run_end_progress window address : address < run_end window address.
Proof.
  unfold run_end. destruct (paged window address) eqn:Paged.
  - exact (proj2 (page_interval address)).
  - unfold region_end. apply folded_boundary_progress.
    unfold paged in Paged. apply orb_false_iff in Paged as [Below _]. apply Z.leb_gt in Below. exact Below.
Qed.

Definition piece_end window stop cursor := Z.min stop (run_end window cursor).
Theorem piece_progress window stop cursor : cursor < stop -> cursor < piece_end window stop cursor <= stop.
Proof. intro Active. unfold piece_end. pose proof (run_end_progress window cursor). lia. Qed.

Theorem piece_does_not_cross_page window stop cursor position :
  paged window cursor = true -> cursor <= position < piece_end window stop cursor ->
  position / page_size = cursor / page_size.
Proof.
  intros Paged Inside. apply same_page_before_end.
  unfold piece_end, run_end in Inside. rewrite Paged in Inside. lia.
Qed.

Theorem piece_stays_in_span window range cursor :
  CheckedArithmetic.beginning range <= cursor < CheckedArithmetic.ending range ->
  CheckedArithmetic.fits (piece_end window (CheckedArithmetic.ending range) cursor) /\
  0 <= cursor - CheckedArithmetic.beginning range /\
  0 < piece_end window (CheckedArithmetic.ending range) cursor - cursor /\
  (cursor - CheckedArithmetic.beginning range) +
    (piece_end window (CheckedArithmetic.ending range) cursor - cursor) <= CheckedArithmetic.length range.
Proof.
  intros [Beginning Active]. pose proof (piece_progress window Active) as Progress.
  split.
  - apply (@CheckedArithmetic.span_cursor_fits range _). lia.
  - unfold CheckedArithmetic.length. lia.
Qed.

Theorem remaining_decreases window range cursor :
  CheckedArithmetic.beginning range <= cursor < CheckedArithmetic.ending range ->
  (Z.to_nat (CheckedArithmetic.ending range - piece_end window (CheckedArithmetic.ending range) cursor) <
   Z.to_nat (CheckedArithmetic.ending range - cursor))%nat.
Proof.
  intros [Beginning Active]. pose proof (piece_progress window Active) as Progress.
  apply Z2Nat.inj_lt; lia.
Qed.

Lemma selected_boundary_le_before address before candidate : select_boundary address before candidate <= before.
Proof.
  unfold select_boundary. destruct (Z.ltb address candidate && Z.ltb candidate before) eqn:Selected; [|lia].
  apply andb_true_iff in Selected as [_ Earlier]. apply Z.ltb_lt in Earlier. lia.
Qed.

Lemma selected_boundary_le_candidate address before candidate :
  address < candidate -> select_boundary address before candidate <= candidate.
Proof.
  intro Forward. unfold select_boundary. rewrite (proj2 (Z.ltb_lt address candidate) Forward). cbn.
  destruct (Z.ltb candidate before) eqn:Earlier; [lia|]. apply Z.ltb_ge in Earlier. lia.
Qed.

Lemma folded_boundary_le_before address candidates : forall before,
  fold_left (select_boundary address) candidates before <= before.
Proof.
  induction candidates as [|candidate rest IH]; intros before; cbn; [lia|].
  pose proof (IH (select_boundary address before candidate)).
  pose proof (selected_boundary_le_before address before candidate). lia.
Qed.

Lemma folded_boundary_le_member address candidates : forall before candidate,
  In candidate candidates -> address < candidate ->
  fold_left (select_boundary address) candidates before <= candidate.
Proof.
  induction candidates as [|head rest IH]; intros before candidate Member Forward; [contradiction|].
  cbn in *. destruct Member as [<-|Member].
  - pose proof (folded_boundary_le_before address rest (select_boundary address before head)).
    pose proof (@selected_boundary_le_candidate address before head Forward). lia.
  - now apply IH.
Qed.

Theorem region_cut_preserves_comparisons window cursor position boundary :
  In boundary (boundaries window) -> cursor <= position < region_end window cursor ->
  Z.leb boundary position = Z.leb boundary cursor.
Proof.
  intros Member Inside. destruct (Z_le_gt_dec boundary cursor) as [Earlier|Later].
  - rewrite (proj2 (Z.leb_le boundary position) ltac:(lia)),
      (proj2 (Z.leb_le boundary cursor) Earlier). reflexivity.
  - assert (region_end window cursor <= boundary) as Cut
      by (unfold region_end; eapply folded_boundary_le_member; [exact Member|lia]).
    assert (Z.leb boundary position = false) by (apply Z.leb_gt; lia).
    assert (Z.leb boundary cursor = false) by (apply Z.leb_gt; lia). congruence.
Qed.

Fixpoint partition_walk window (remaining : nat) cursor stop : list (Z * Z) :=
  match remaining with
  | O => []
  | S rest => if Z.ltb cursor stop then
      let next := piece_end window stop cursor in (cursor,next) :: partition_walk window rest next stop
    else []
  end.
Definition partition window range :=
  partition_walk window (Z.to_nat (CheckedArithmetic.length range))
    (CheckedArithmetic.beginning range) (CheckedArithmetic.ending range).

(** A content specification: exact consecutive coverage, positive chunks and
    per-chunk boundary enclosure. The recursive budget is input length, not
    an independent cap, and sufficient budget is proved below. *)
Inductive covers (window : layout) : Z -> Z -> list (Z * Z) -> Prop :=
| Covers_empty : forall position, covers window position position []
| Covers_piece : forall first next stop rest,
    first < next <= stop -> next <= run_end window first ->
    covers window next stop rest -> covers window first stop ((first,next) :: rest).

Theorem partition_walk_covers window remaining : forall cursor stop,
  cursor <= stop -> (Z.to_nat (stop - cursor) <= remaining)%nat ->
  covers window cursor stop (partition_walk window remaining cursor stop).
Proof.
  induction remaining as [|remaining IH]; intros cursor stop Ordered Budget.
  - cbn. assert (Z.to_nat (stop - cursor) = 0%nat) as Empty by lia.
    pose proof (Z2Nat.id (stop - cursor) ltac:(lia)) as Convert.
    rewrite Empty in Convert. cbn in Convert. assert (cursor = stop) by lia.
    subst. constructor.
  - cbn. destruct (Z.ltb cursor stop) eqn:Active.
    + apply Z.ltb_lt in Active. pose proof (piece_progress window Active) as Progress.
      constructor; [exact Progress|unfold piece_end; lia|].
      apply IH; [lia|].
      assert (Z.to_nat (stop - piece_end window stop cursor) < Z.to_nat (stop - cursor))%nat
        by (apply Z2Nat.inj_lt; lia).
      lia.
    + apply Z.ltb_ge in Active. assert (cursor = stop) by lia. subst. constructor.
Qed.

Theorem partition_covers window range :
  covers window (CheckedArithmetic.beginning range) (CheckedArithmetic.ending range) (partition window range).
Proof.
  unfold partition, CheckedArithmetic.length. apply partition_walk_covers;
    [pose proof (CheckedArithmetic.ordered range); lia|lia].
Qed.

Definition total_length (pieces : list (Z * Z)) :=
  fold_right (fun piece total => snd piece - fst piece + total) 0 pieces.

Theorem covered_length window first stop pieces : covers window first stop pieces -> total_length pieces = stop - first.
Proof.
  intro Cover. induction Cover.
  - unfold total_length. cbn. lia.
  - change (next - first + total_length rest = stop - first). lia.
Qed.

Theorem partition_length window range : total_length (partition window range) = CheckedArithmetic.length range.
Proof. apply (@covered_length window _ _ _). apply partition_covers. Qed.

Theorem covered_positions window first stop pieces : covers window first stop pieces ->
  forall start finish, In (start,finish) pieces -> first <= start /\ start < finish /\ finish <= stop.
Proof.
  intro Cover. induction Cover; intros start finish Member; [contradiction|].
  destruct Member as [Same|Member].
  - inversion Same; subst. lia.
  - apply IHCover in Member. lia.
Qed.

Theorem partition_callbacks_in_bounds window range start finish :
  In (start,finish) (partition window range) ->
  0 <= start - CheckedArithmetic.beginning range /\ 0 < finish - start /\
  (start - CheckedArithmetic.beginning range) + (finish - start) <= CheckedArithmetic.length range.
Proof.
  intro Member. pose proof (@covered_positions window _ _ _ (partition_covers window range) start finish Member) as Bounds.
  unfold CheckedArithmetic.length. lia.
Qed.
