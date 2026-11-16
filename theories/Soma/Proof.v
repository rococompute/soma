(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Proof sentences, for .exp files

    Imported in .exp files only (toplevel/ccompile.ml). A proof is
    written as sentences that say what they do, and each sentence is
    checked: one that states a goal or a fact fails unless the statement
    is the goal or holds. The sentences are tactics, and can be mixed with
    any other tactic.

    - [Take x : T.] names the next variable of the goal, a [T].
    - [Assume that P as H.] names the next hypothesis of the goal, [P].
    - [We need to show that P.] states the goal, [P], perhaps unfolded or
      computed.
    - [Here H means that P.] states the hypothesis [H], perhaps unfolded
      or computed, as [P].
    - [It holds that P as H.] proves [P] and names it [H].
    - [It suffices to show that P.] replaces the goal with [P], which
      proves it.
    - [We conclude that P.] states the goal and proves it.
    - [Computing, we need to show that P.] and [Computing, we conclude
      that P.] compute the goal ([simpl]) first: for a goal that is [P]
      once evaluated.
    - [By t, ...] in front of the last three uses [t], a hypothesis or a
      lemma, to prove the statement: [t] applied, or rewritten with.
    - [We show that P as H.] and [It suffices to show that P as H.] are
      for a statement that is proved by sentences of its own, in braces
      right after: [P] for the first, the goal from [H : P] for the
      second.
    - [Choose x := t.] proves an [exists x, ...] goal with [t].
    - [Obtain a and b from x.] takes [x] (a pair, a [{a | P a}], an
      [exists a, P a], an [A /\ B]) apart into [a] and [b].
    - [We prove each part.] splits an [A /\ B] goal into [A] and [B].
    - [We consider each case of x.] is a case for each constructor of
      [x]; [We consider whether a < b as H.] (or [<=], [=], for numbers)
      is a case with [H : a < b] and one with its opposite, and in each,
      [a <? b] is [true] or [false].
    - [The rest follows.] searches for the rest of the proof: it takes
      and assumes what the goal gives, then proves it with [soma_auto], a
      hypothesis or a lemma of the loaded libraries. It reports the proof
      it found as sentences (soma build -v prints them, soma build --fill
      writes them in its place), or what is still to show.
    - [We use induction on x.] is a case for each constructor of [x],
      with its arguments and induction hypotheses to [Take] and
      [Assume]; [We use strong induction on n.] (for a number) is one
      case, for [n], assuming the statement for every smaller number.

    - [computed] proves an equation that holds by computation, such as an
      example of what a function gives, [f 3 = "three"], perhaps for every
      value of some variables ([forall x, ...]): the kernel
      computes both sides when the proof ends ([Qed]), once. [reflexivity]
      would also compute them as it is applied, so that this check takes
      twice as long. An equation that does not hold fails at [Qed]: "The
      term eq_refl ... has type ... while it is expected to have type ...".

    "Proves" means: by [soma_auto], which tries, in turn, the hypotheses,
    computation, equalities, linear then non-linear arithmetic ([lia],
    [ring], [nia]) and propositional logic. A step [soma_auto] cannot take
    is split into smaller sentences, or given with [By].

    In a .exp file, a tactic acts on one goal at a time: with several
    goals open, each is focused with a bullet ([-], [+], [*]) or braces. *)

From Stdlib Require Import Arith Lia Lra.
Declare ML Module "soma-runtime.plugins.soma_proof".

(** ** Computed equations *)

(* The proof term is checked by the kernel at Qed, as every proof is; this
   only leaves out the tactic's own check, which is the same computation.
   The term is [eq_refl] of the right side, the expected value, as
   reflexivity's is: the kernel then computes the left side towards it.
   Of the left side, it can compute much more: a [sha256 (sha256 "x")] on
   both sides, computed rather than compared. *)
Ltac computed :=
  intros;
  lazymatch goal with
  | |- @eq ?T _ ?b => exact_no_check (@eq_refl T b)
  | |- ?g => fail "computed: the goal is not an equation:" g
  end.

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
        | (cbn in *; lia)
        | lra
        | tauto
        | (simpl in *; congruence)
        | easy ].

(** Rewriting with [t] at most 10 times: [rewrite !t] does not stop for
    an equation that applies again after itself, like commutativity *)
Ltac soma_rewrite t tac := rewrite t by tac; do 9 (try rewrite t by tac).
Ltac soma_rewrite_back t tac := rewrite <- t by tac; do 9 (try rewrite <- t by tac).
Ltac soma_rewrite_all t tac := rewrite t in * by tac; do 9 (try rewrite t in * by tac).
Ltac soma_rewrite_all_back t tac := rewrite <- t in * by tac; do 9 (try rewrite <- t in * by tac).

(** With [t]: [t] itself, [t] applied, or [t] rewritten with, in the
    goal or everywhere, after computing or not; the conditions of [t] are
    proved too *)
Ltac soma_by t :=
  solve [ exact t
        | (apply t; soma_auto)
        | (eapply t; solve [eassumption | soma_auto])
        | (soma_rewrite t ltac:(soma_auto); soma_auto)
        | (soma_rewrite_back t ltac:(soma_auto); soma_auto)
        | (soma_rewrite_all t ltac:(soma_auto); soma_auto)
        | (soma_rewrite_all_back t ltac:(soma_auto); soma_auto)
        | (simpl; soma_rewrite t ltac:(soma_auto); soma_auto)
        | (pose proof t; soma_auto) ].

(** What the search for [The rest follows.] tries for each lemma: quick,
    as it tries many. A step it proves this way, [soma_by] proves too. *)
Ltac soma_quick :=
  solve [ assumption | reflexivity | discriminate | congruence | lia | lra
        | (simpl; reflexivity) | (cbn; lia) ].

Ltac soma_by_quick t :=
  solve [ exact t
        | (apply t; soma_quick)
        | (soma_rewrite t ltac:(soma_quick); soma_quick)
        | (soma_rewrite_back t ltac:(soma_quick); soma_quick) ].

Tactic Notation "The" "rest" "follows" := soma_rest.

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

Tactic Notation "Computing" "," "we" "need" "to" "show" "that" lconstr(P) :=
  simpl; soma_goal_is P.

Tactic Notation "Computing" "," "we" "conclude" "that" lconstr(P) :=
  simpl; soma_goal_is P;
  first [ soma_auto | fail 1 "This does not follow (prove it in smaller steps, or with By):" P ].

Tactic Notation "By" lconstr(t) "," "we" "conclude" "that" lconstr(P) :=
  soma_goal_is P;
  first [ soma_by t | fail 1 "This does not follow from" t ":" P ].

(** ** Facts *)

Tactic Notation "It" "holds" "that" lconstr(P) "as" ident(H) :=
  first [ assert (H : P) by soma_auto
        | fail 1 "This does not follow (prove it in smaller steps, or with By):" P ].

Tactic Notation "By" lconstr(t) "," "it" "holds" "that" lconstr(P) "as" ident(H) :=
  first [ assert (H : P) by soma_by t | fail 1 "This does not follow from" t ":" P ].

Tactic Notation "It" "suffices" "to" "show" "that" lconstr(P) :=
  let H := fresh "H" in
  first [ enough (H : P) by soma_by H
        | fail 1 "The goal does not follow from" P ].

Tactic Notation "By" lconstr(t) "," "it" "suffices" "to" "show" "that" lconstr(P) :=
  let H := fresh "H" in
  first [ enough (H : P) by soma_by t
        | fail 1 "The goal does not follow from" t "and" P ].

(** Statements proved by sentences of their own, in braces right after *)

Tactic Notation "We" "show" "that" lconstr(P) "as" ident(H) :=
  assert (H : P).

Tactic Notation "It" "suffices" "to" "show" "that" lconstr(P) "as" ident(H) :=
  enough (H : P).

Tactic Notation "Here" ident(H) "means" "that" lconstr(P) :=
  first [ change P in H
        | let Q := type of H in fail 1 "The hypothesis" H "is" Q "and not" P ].

(** ** Witnesses and parts *)

Tactic Notation "Choose" ident(x) ":=" lconstr(t) := exists t.

Tactic Notation "Obtain" ident(a) "and" ident(b) "from" constr(x) :=
  destruct x as [a b].

Tactic Notation "We" "prove" "each" "part" := split.

(** ** Cases and induction *)

Tactic Notation "We" "consider" "each" "case" "of" lconstr(x) := destruct x.

(** [We consider each case of parse s as parsed.]: each case, with what
    [parse s] is in it as [parsed] ([parsed : parse s = Some n], ...) *)
Tactic Notation "We" "consider" "each" "case" "of" lconstr(x) "as" ident(H) :=
  destruct x eqn:H.

Ltac soma_whether P H :=
  lazymatch P with
  | ?a < ?b => destruct (Nat.ltb_spec a b) as [H|H]
  | ?a <= ?b => destruct (Nat.leb_spec a b) as [H|H]
  | ?a = ?b => destruct (Nat.eqb_spec a b) as [H|H]
  | _ => fail "We can consider whether a < b, a <= b or a = b, for numbers, not" P
  end.

Tactic Notation "We" "consider" "whether" lconstr(P) "as" ident(H) := soma_whether P H.

(* [x] goes back into the goal, with what depends on it, which each case
   then takes and assumes again *)
Tactic Notation "We" "use" "induction" "on" ident(x) :=
  generalize dependent x; intro x; elim x; clear x.

Tactic Notation "We" "use" "strong" "induction" "on" ident(x) :=
  generalize dependent x;
  lazymatch goal with
  | |- forall y : nat, @?P y => apply (well_founded_ind lt_wf P); cbv beta
  | _ => fail "Strong induction is on a number"
  end.

(** ** One goal at a time *)

#[export] Set Default Goal Selector "!".

(* A theorem whose evidence is a gradual primitive ([unk], [raise], a cast
   to its statement) is not proved: an error in .exp files, rather than
   Rocq's warning (vernac/declare.ml) *)
#[export] Set Warnings "+gradual-proof".

(* [lia] and [nia] keep no cache files next to the program *)
#[export] Unset Lia Cache.
#[export] Unset Nia Cache.
