(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: [load_ext ~state f] loads the .ext file [f] as [Load] does:
    in a module of its own, whose macros are then in scope *)
val load_ext : state:Vernac.State.t -> string -> Vernac.State.t

(** Soma: FILE.ext, the macros of FILE.soma, when there is one *)
val ext_of_program : string -> string option

  (** [load_init_vernaculars opts ~state] Load vernaculars from
   the init (rc) file *)
val load_init_vernaculars : Coqargs.t -> state:Vernac.State.t-> Vernac.State.t
