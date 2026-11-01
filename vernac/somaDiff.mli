(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: [soma diff OLD NEW], two versions of a project compared by what the
    kernel checked of them (see the implementation). *)

(** [run [old; new]]: each a tag, PATH@VERSION, or a folder with a soma.toml.
    Prints the report. It compiles them, and changes nothing of a project. *)
val run : string list -> unit
