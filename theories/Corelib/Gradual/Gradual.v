(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Gradual CIC, normalization-sacrificing variant (GCIC^G)

    Importing this file turns Rocq into a gradual dependently typed
    language following Lennon-Bertrand, Maillard, Tabareau and Tanter,
    "Gradualizing the Calculus of Inductive Constructions" (TOPLAS 2022).

    Their "fire triangle of graduality" says that a gradual extension of
    CIC cannot have all three of
    - conservativity over CIC,
    - graduality (embedding-projection pairs between more and less
      precise types), and
    - (strong) normalization.
    This development keeps the first two and gives up normalization: the
    unknown type [Any] can contain [Any -> Any] in the same universe, so
    [omega] below is well-typed and loops.

    The kernel only knows three axioms, registered below, and reduces them
    following the cast calculus. When [Gradual Typing] is set, the
    elaborator accepts terms whose types are merely _consistent_ (equal up
    to the unknown) with the expected type, inserting [cast]s.

    Caveats:
    - The theory is (intentionally) logically inconsistent once [unknown] or
      [err] are used: [unknown False : False]. Use [Print Assumptions] to
      see whether a development depends on them.
    - The VM and native compilation treat the primitives as opaque, so
      under [Gradual Typing] [vm_compute], [native_compute] and [Compute]
      fall back to [cbv]. *)

Require Import Corelib.Init.Prelude.

(** A single global universe bounds the types the primitives work on. *)
Universe gradual.

(** [unknown A] is the unknown term [?_A] of type [A]. *)
Axiom unknown : forall A : Type@{gradual}, A.

(** [err A] is the runtime error [err_A] of type [A]. *)
Axiom err : forall A : Type@{gradual}, A.

(** [cast A B t] is the cast [<B <= A> t]. *)
Axiom cast : forall A B : Type@{gradual}, A -> B.

Register unknown as kernel.gradual_unknown.
Register err as kernel.gradual_err.
Register cast as kernel.gradual_cast.

(** The unknown type, [?_Type] in GCIC. Each occurrence lives in a fresh
    universe. *)
Abbreviation Any := (unknown Type).

(** The unknown term at the expected type. *)
Abbreviation unk := (unknown _).

(** Raising an error at the expected type. *)
Abbreviation raise := (err _).

#[export] Set Gradual Typing.
