(** A partial-write contract for host sockets. This specifies byte
    accounting, not delivery, syscall correctness, or network fairness.
    The runtime conformance test exercises Soma.Host's actual socket shim. *)
From Stdlib Require Import Strings.String Arith Lia List.
Require Import Soma.Wire.

Module SocketWrites.
Definition advance (pending : string) (count : nat) : option (string * string) :=
  Wire.split_at count pending.

Lemma split_preserves : forall count pending sent rest,
  Wire.split_at_walk count pending = Some (sent, rest) ->
  String.append sent rest = pending /\ String.length sent = count.
Proof.
  induction count as [|count IH]; intros pending sent rest H.
  - cbn [Wire.split_at_walk] in H. injection H as <- <-. split; reflexivity.
  - destruct pending as [|a pending]; cbn [Wire.split_at_walk] in H; [discriminate|].
    destruct (Wire.split_at_walk count pending) as [[part after]|] eqn:E; [|discriminate].
    injection H as <- <-. destruct (IH pending part after E) as [Join Size].
    cbn [String.append String.length]. split; [now rewrite Join|lia].
Qed.

Theorem advance_preserves_bytes : forall pending count sent rest,
  advance pending count = Some (sent, rest) ->
  String.append sent rest = pending /\ String.length sent = count.
Proof.
  intros pending count sent rest H. unfold advance in H. rewrite Wire.split_at_walk_eq in H.
  now apply split_preserves in H.
Qed.

Theorem advance_past_end : forall pending count,
  String.length pending < count -> advance pending count = None.
Proof.
  intros pending count H. unfold advance, Wire.split_at.
  assert (Nat.leb count (String.length pending) = false) as E by (apply Nat.leb_gt; lia).
  now rewrite E.
Qed.

Inductive write_answer := Retry | Wrote (count : nat) | Failed.
Definition write_step (pending : string) (answer : write_answer) : option (string * string) :=
  match answer with
  | Retry => Some (String.EmptyString, pending)
  | Wrote count => advance pending count
  | Failed => None
  end.

Fixpoint writes (pending : string) (answers : list write_answer) : option (string * string) :=
  match answers with
  | nil => Some (String.EmptyString, pending)
  | cons answer rest =>
      match write_step pending answer with
      | None => None
      | Some (sent, pending) =>
          match writes pending rest with
          | None => None
          | Some (more, kept) => Some (String.append sent more, kept)
          end
      end
  end.

Theorem writes_preserve_bytes : forall answers pending sent rest,
  writes pending answers = Some (sent, rest) -> String.append sent rest = pending.
Proof.
  induction answers as [|answer answers IH]; intros pending sent rest H.
  - cbn [writes] in H. injection H as <- <-. reflexivity.
  - cbn [writes] in H.
    destruct (write_step pending answer) as [[part after]|] eqn:E; [|discriminate].
    destruct (writes after answers) as [[more kept]|] eqn:W; [|discriminate].
    injection H as <- <-. rewrite Wire.append_assoc_str, (IH _ _ _ W).
    destruct answer; cbn [write_step] in E.
    + injection E as <- <-. reflexivity.
    + exact (proj1 (advance_preserves_bytes _ _ _ _ E)).
    + discriminate.
Qed.
End SocketWrites.
