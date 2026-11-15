(** Recovery contract for an initialized, two-bank store.

    A committed bank remains intact while the inactive bank is written.
    A candidate bank is either older/invalid, or is the complete new
    snapshot. Under that classification premise recovery chooses exactly
    the old or new snapshot, never a mixture. This does not prove that
    native checksum validation establishes the premise, or that a device
    persists writes in program order. Runtime cut tests check those paths
    for the modeled ordered-sector device, including torn writes. *)
From Stdlib Require Import Arith Lia Strings.String List.
Require Import Soma.Sandbox.

Module SnapshotRecovery.
Record snapshot := Snapshot { generation : nat; files : Files.state }.
Inductive bank := Empty | Invalid | Valid (snapshot : snapshot).
Definition recover (first second : bank) : option snapshot :=
  match first, second with
  | Valid a, Valid b => if Nat.leb (generation b) (generation a) then Some a else Some b
  | Valid a, _ => Some a
  | _, Valid b => Some b
  | _, _ => None
  end.
Definition older_than (current : snapshot) (candidate : bank) : Prop :=
  match candidate with Valid old => generation old < generation current | _ => True end.

Lemma recover_left : forall current candidate,
  older_than current candidate -> recover (Valid current) candidate = Some current.
Proof.
  intros current [| |old] H; cbn [older_than recover] in *; try reflexivity.
  assert (Nat.leb (generation old) (generation current) = true) as E by (apply Nat.leb_le; lia).
  now rewrite E.
Qed.
Lemma recover_right : forall current candidate,
  older_than current candidate -> recover candidate (Valid current) = Some current.
Proof.
  intros current [| |old] H; cbn [older_than recover] in *; try reflexivity.
  assert (Nat.leb (generation current) (generation old) = false) as E by (apply Nat.leb_gt; lia).
  now rewrite E.
Qed.

Definition candidate_after_cut (old fresh : snapshot) (candidate : bank) : Prop :=
  older_than old candidate \/ candidate = Valid fresh.

Theorem interrupted_commit_left : forall old fresh candidate,
  generation old < generation fresh -> candidate_after_cut old fresh candidate ->
  recover (Valid old) candidate = Some old \/ recover (Valid old) candidate = Some fresh.
Proof.
  intros old fresh candidate New [Before|After].
  - left. now apply recover_left.
  - subst candidate. right. apply recover_right. exact New.
Qed.
Theorem interrupted_commit_right : forall old fresh candidate,
  generation old < generation fresh -> candidate_after_cut old fresh candidate ->
  recover candidate (Valid old) = Some old \/ recover candidate (Valid old) = Some fresh.
Proof.
  intros old fresh candidate New [Before|After].
  - left. now apply recover_right.
  - subst candidate. right. apply recover_left. exact New.
Qed.

Definition written (old : snapshot) (name contents : string) : snapshot :=
  Snapshot (S (generation old)) (Files.write name contents (files old)).

Theorem committed_write_readback : forall old name contents recovered,
  recover (Valid old) (Valid (written old name contents)) = Some recovered ->
  Files.read name (files recovered) = Some contents.
Proof.
  intros old name contents recovered H.
  rewrite recover_right in H by (cbn [older_than written generation]; lia).
  injection H as <-. cbn [written files]. apply Files.read_write.
Qed.

Theorem committed_write_preserves_other : forall old name other contents recovered,
  name <> other ->
  recover (Valid old) (Valid (written old name contents)) = Some recovered ->
  Files.read other (files recovered) = Files.read other (files old).
Proof.
  intros old name other contents recovered Different H.
  rewrite recover_right in H by (cbn [older_than written generation]; lia).
  injection H as <-. cbn [written files]. apply Files.read_write_other. apply String.eqb_neq. congruence.
Qed.
(** Abstract ordered-sector commit protocol. Payload writes invalidate the
    inactive bank; the header can seal it only once all payload sectors
    have completed. Acknowledgment is possible only after sealing. *)
Record cursor := Cursor {
  remaining : nat;
  sealed : bool;
  acknowledged : bool;
  candidate : bank
}.
Inductive event := Payload | Header | Acknowledge.
Definition start (sectors : nat) (inactive : bank) : cursor :=
  Cursor sectors false false inactive.
Definition step (fresh : snapshot) (action : event) (state : cursor) : option cursor :=
  if acknowledged state then None else
  match action with
  | Payload => if sealed state then None else
      match remaining state with
      | 0 => None
      | S count => Some (Cursor count false false Invalid)
      end
  | Header => if sealed state then None else
      match remaining state with
      | 0 => Some (Cursor 0 true false (Valid fresh))
      | S _ => None
      end
  | Acknowledge => if sealed state
      then Some (Cursor (remaining state) true true (candidate state)) else None
  end.
Fixpoint run (fresh : snapshot) (actions : list event) (state : cursor) : option cursor :=
  match actions with
  | nil => Some state
  | cons action rest => match step fresh action state with
      | None => None | Some next => run fresh rest next end
  end.
Definition invariant (old fresh : snapshot) (state : cursor) : Prop :=
  candidate_after_cut old fresh (candidate state) /\
  (sealed state = true -> candidate state = Valid fresh) /\
  (acknowledged state = true -> sealed state = true).

Lemma step_invariant : forall old fresh action state next,
  invariant old fresh state -> step fresh action state = Some next ->
  invariant old fresh next.
Proof.
  intros old fresh action [count seal ack bank] next [Cut [Sealed Ack]] H.
  unfold step in H; cbn [acknowledged sealed remaining candidate] in *.
  destruct ack; [discriminate|].
  destruct action; destruct seal; try discriminate.
  - destruct count; [discriminate|]. injection H as <-.
    unfold invariant, candidate_after_cut; cbn [candidate older_than sealed acknowledged]. intuition congruence.
  - destruct count; [|discriminate]. injection H as <-.
    unfold invariant, candidate_after_cut; cbn [candidate sealed acknowledged]. intuition congruence.
  - injection H as <-. unfold invariant; cbn [candidate sealed acknowledged]. intuition congruence.
Qed.

Lemma run_invariant : forall old fresh actions state final,
  invariant old fresh state -> run fresh actions state = Some final ->
  invariant old fresh final.
Proof.
  intros old fresh actions. induction actions as [|action actions IH]; intros state final Inv H.
  - cbn [run] in H. now injection H as <-.
  - cbn [run] in H. destruct (step fresh action state) as [next|] eqn:E; [|discriminate].
    apply (IH next final); [eapply step_invariant; eauto|exact H].
Qed.

Theorem every_commit_prefix_recovers_old_or_new : forall old fresh inactive sectors actions final,
  generation old < generation fresh -> older_than old inactive ->
  run fresh actions (start sectors inactive) = Some final ->
  recover (Valid old) (candidate final) = Some old \/
  recover (Valid old) (candidate final) = Some fresh.
Proof.
  intros old fresh inactive sectors actions final New Older H.
  apply interrupted_commit_left; [exact New|].
  assert (invariant old fresh (start sectors inactive)) as Initial.
  { unfold invariant, start, candidate_after_cut; cbn [candidate sealed acknowledged]. intuition congruence. }
  exact (proj1 (run_invariant _ _ _ _ _ Initial H)).
Qed.

Theorem acknowledged_commit_recovers_new : forall old fresh inactive sectors actions final,
  generation old < generation fresh -> older_than old inactive ->
  run fresh actions (start sectors inactive) = Some final ->
  acknowledged final = true -> recover (Valid old) (candidate final) = Some fresh.
Proof.
  intros old fresh inactive sectors actions final New Older H Ack.
  assert (invariant old fresh (start sectors inactive)) as Initial.
  { unfold invariant, start, candidate_after_cut; cbn [candidate sealed acknowledged]. intuition congruence. }
  destruct (run_invariant _ _ _ _ _ Initial H) as [_ [Sealed Acknowledged]].
  rewrite (Sealed (Acknowledged Ack)). apply recover_right. exact New.
Qed.
End SnapshotRecovery.
