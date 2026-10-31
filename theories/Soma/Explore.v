(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Exploring a program as a state machine, [Soma.Explore]

    Not part of the prelude. A [model] says how a program goes: the
    inputs it may be given (its scope, as in Alloy), the state each
    starts it in, the actions that may be taken in any state and what
    each does, and what should hold of every state ([invariants]) and of
    every action, before and after ([steps]). [Explore model.] tries
    them all, as TLC does for TLA+: from every input, every sequence of
    actions up to [depth], evaluating the states and the properties as
    Soma evaluates a term. A state, or a property, that is a run-time
    error ([raise], a cast that failed) is found as a violation is, with
    what went wrong.

    The command reports each violation with the input and the actions
    that lead to it, and fails when there is one; else it says what it
    explored (plugins/soma_explore). *)

From Stdlib Require Strings.String.
Require Import Soma.Strings Soma.Lists.

Record model (Input State Action : Type) := {
  (** the inputs to start from *)
  inputs : list Input;
  (** the state an input starts in *)
  initial : Input -> State;
  (** the actions that may be taken, in any state *)
  actions : list Action;
  (** what an action does *)
  transition : Action -> State -> State;
  (** how many actions in a row, at most *)
  depth : nat;
  (** what every state is, by name *)
  invariants : list (string * (State -> bool));
  (** what every action does, by name: from the state before to the one after *)
  steps : list (string * (State -> State -> bool))
}.

Arguments inputs {Input State Action} m.
Arguments initial {Input State Action} m i.
Arguments actions {Input State Action} m.
Arguments transition {Input State Action} m a s.
Arguments depth {Input State Action} m.
Arguments invariants {Input State Action} m.
Arguments steps {Input State Action} m.

Declare ML Module "soma-runtime.plugins.soma_explore".
