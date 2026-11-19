(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Ordered default candidates, shared with conservative build freshness checks.
    Selection still chooses the first readable file. *)
val default_candidates : warn:(string -> unit) -> string list

val load_rcfile : rcfile:(string option) -> state:Vernac.State.t -> Vernac.State.t
