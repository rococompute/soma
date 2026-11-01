(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: [soma search QUERY [FILE]]: definitions and theorems by name or by the
    shape of their types (see the implementation). *)

(** The command: [run args], arguments as given *)
val run : string list -> unit

(** Written at the end of a compilation, when [$SOMA_SEARCH] is a query: what it
    finds, in what was checked, to [$SOMA_SEARCH_OUT] *)
val report : unit -> unit
