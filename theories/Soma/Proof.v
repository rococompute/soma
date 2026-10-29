(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Proof sentences, for .proof files

    Imported in .proof files only (toplevel/ccompile.ml). A proof is
    written as sentences that say what they do, and each sentence is
    checked: one that states a goal or a fact fails unless the statement
    is the goal or holds. The sentences are tactics, and can be mixed with
    any other tactic.

    - [Take x : T.] names the next variable of the goal, a [T].
    - [Assume that P as H.] names the next hypothesis of the goal, [P].
    - [We need to show that P.] states the goal, [P], perhaps unfolded or
      computed.
    - [It holds that P as H.] proves [P] and names it [H].
    - [It suffices to show that P.] replaces the goal with [P], which
      proves it.
    - [We conclude that P.] states the goal and proves it.
    - [By t, ...] in front of the last three uses [t], a hypothesis or a
      lemma, to prove the statement.
    - [Choose x := t.] proves an [exists x, ...] goal with [t].
    - [Obtain a and b from x.] takes [x] (a pair, a [{a | P a}], an
      [exists a, P a], an [A /\ B]) apart into [a] and [b].

    "Proves" means: by [soma_auto], which tries, in turn, the hypotheses,
    computation, equalities, linear then non-linear arithmetic ([lia],
    [ring], [nia]) and propositional logic. A step [soma_auto] cannot take
    is split into smaller sentences, or given with [By].

    In a .proof file, a tactic acts on one goal at a time: with several
    goals open, each is focused with a bullet ([-], [+], [*]) or braces. *)

From Stdlib Require Import Arith Lia.

(** ** What "proves" means *)

Ltac soma_auto :=
  solve [ assumption
        | reflexivity
        | discriminate
        | congruence
        | (subst; assumption)
        | lia
        | ring
        | (simpl; ring)
        | nia
        | (simpl in *; nia)
        | tauto
        | (simpl in *; congruence)
        | easy ].

(** With [t]: [t] itself, [t] applied, or [t] rewritten with *)
Ltac soma_by t :=
  solve [ exact t
        | (apply t; soma_auto)
        | (rewrite t in *; soma_auto)
        | (rewrite <- t in *; soma_auto)
        | (pose proof t; soma_auto) ].

(** ** Naming what the goal gives *)

Tactic Notation "Take" ident(x) ":" lconstr(T) :=
  intro x;
  first [ change T in x
        | let U := type of x in fail 1 "The next variable is a" U "and not a" T ].

Tactic Notation "Assume" "that" lconstr(P) "as" ident(H) :=
  intro H;
  first [ change P in H
        | let Q := type of H in fail 1 "The next hypothesis is" Q "and not" P ].

(** ** Stating the goal *)

Ltac soma_goal_is P :=
  lazymatch goal with
  | |- ?G => tryif change P then idtac else fail "The goal is" G "and not" P
  end.

Tactic Notation "We" "need" "to" "show" "that" lconstr(P) :=
  soma_goal_is P.

Tactic Notation "We" "conclude" "that" lconstr(P) :=
  soma_goal_is P;
  first [ soma_auto | fail 1 "This does not follow (prove it in smaller steps, or with By):" P ].

Tactic Notation "By" constr(t) "," "we" "conclude" "that" lconstr(P) :=
  soma_goal_is P;
  first [ soma_by t | fail 1 "This does not follow from" t ":" P ].

(** ** Facts *)

Tactic Notation "It" "holds" "that" lconstr(P) "as" ident(H) :=
  first [ assert (H : P) by soma_auto
        | fail 1 "This does not follow (prove it in smaller steps, or with By):" P ].

Tactic Notation "By" constr(t) "," "it" "holds" "that" lconstr(P) "as" ident(H) :=
  first [ assert (H : P) by soma_by t | fail 1 "This does not follow from" t ":" P ].

Tactic Notation "It" "suffices" "to" "show" "that" lconstr(P) :=
  let H := fresh "H" in
  first [ enough (H : P) by soma_by H
        | fail 1 "The goal does not follow from" P ].

Tactic Notation "By" constr(t) "," "it" "suffices" "to" "show" "that" lconstr(P) :=
  let H := fresh "H" in
  first [ enough (H : P) by (pose proof t; soma_by H)
        | fail 1 "The goal does not follow from" P "and" t ].

(** ** Witnesses and parts *)

Tactic Notation "Choose" ident(x) ":=" lconstr(t) := exists t.

Tactic Notation "Obtain" ident(a) "and" ident(b) "from" constr(x) :=
  destruct x as [a b].

(** ** One goal at a time *)

#[export] Set Default Goal Selector "!".

(* [lia] and [nia] keep no cache files next to the program *)
#[export] Unset Lia Cache.
#[export] Unset Nia Cache.
