(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Orchestration: what a run of an image came to, and what to do next

    Not part of the prelude. [soma run --supervise FILE] runs the image of
    a program that requires [Sandbox], and when the run ends, asks the
    program's [restart_policy] (or [default_policy 3 1024]) what to do with
    the [outcome]: be done, or run the image again, perhaps with more
    memory. The outcome is the one soma run says (from the image's events,
    toplevel/somaMirage.ml), as a value. As a policy is a function of
    Soma, what it does can be proved: [default_policy] below never runs
    again what would fail again, stops after [limit] restarts, and never
    asks for more than [ceiling] MB. *)

From Stdlib Require Import Arith.
From Soma Require Import Strings.

(** Why a run failed *)
Inductive failure : Type :=
| CastFailure (expected actual : string)   (* a cast: expected, but got *)
| Raised                                   (* the program reached [raise] *)
| Unknown                                  (* the program reached [unk] *)
| StackOverflow                            (* a recursion too deep *)
| OutOfMemory (memory_mb live_mb : nat)    (* the image's memory, and the last live memory reported *)
| Crashed (reason : string).               (* an exception, or stopped without saying why *)

(** What a run came to *)
Inductive outcome : Type :=
| Finished                   (* [main] ended *)
| Exited (code : nat)        (* the program's [exit code] *)
| Failed (f : failure)
| Stopped.                   (* stopped from outside (kill, Ctrl-C) *)

(** What to do next *)
Inductive decision : Type :=
| Done                         (* do not run it again *)
| Restart                      (* run it again, as it was *)
| RestartWith (memory_mb : nat). (* run it again with this much memory *)

(** A policy decides from the outcome, the image's memory (MB) and how many
    times it was restarted already *)
Definition policy := outcome -> nat -> nat -> decision.

(** A failure that would happen again on a run of the same program with the
    same input: running it again would not help *)
Definition deterministic (o : outcome) : bool :=
  match o with
  | Failed (CastFailure _ _) | Failed Raised | Failed Unknown | Failed StackOverflow => true
  | _ => false
  end.

(** At most [limit] restarts; never what is deterministic, nor what ended
    well or was stopped; after running out of memory, twice the memory, up
    to [ceiling] MB, and no more once at [ceiling]. *)
Definition default_policy (limit ceiling : nat) : policy :=
  fun o memory restarts =>
    if Nat.leb limit restarts then Done
    else if deterministic o then Done
    else match o with
         | Finished | Exited 0 | Stopped => Done
         | Failed (OutOfMemory _ _) =>
           if Nat.leb ceiling memory then Done else RestartWith (Nat.min ceiling (2 * memory))
         | _ => Restart
         end.

(** ** What [default_policy] does *)

Lemma default_never_reruns_deterministic : forall limit ceiling o memory restarts,
  deterministic o = true -> default_policy limit ceiling o memory restarts = Done.
Proof.
  intros limit ceiling o memory restarts H. unfold default_policy.
  destruct (Nat.leb limit restarts); [reflexivity |]. rewrite H. reflexivity.
Qed.

Lemma default_stops_after_limit : forall limit ceiling o memory restarts,
  limit <= restarts -> default_policy limit ceiling o memory restarts = Done.
Proof.
  intros limit ceiling o memory restarts H. unfold default_policy.
  apply Nat.leb_le in H. rewrite H. reflexivity.
Qed.

Lemma default_within_ceiling : forall limit ceiling o memory restarts m,
  default_policy limit ceiling o memory restarts = RestartWith m -> m <= ceiling.
Proof.
  intros limit ceiling o memory restarts m. unfold default_policy.
  destruct (Nat.leb limit restarts); [discriminate |].
  destruct (deterministic o); [discriminate |].
  destruct o as [| [|] | [] |]; try discriminate.
  destruct (Nat.leb ceiling memory); [discriminate |].
  intros H. injection H as <-. apply Nat.le_min_l.
Qed.
