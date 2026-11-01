(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: the hash of a definition, of what the kernel checked rather than of
    the file that says it (see the implementation). *)

(** SHA-256, in hexadecimal *)
val sha256 : string -> string

(** Written at the end of a compilation, when [$SOMA_HASH] is a file: to it,
    a line for each definition of the file being compiled and of the files
    of its project and its dependencies that it imports. [soma hash] asks for
    it, and [soma diff] with [$SOMA_HASH_FIELDS]. *)
val report : unit -> unit

(** The contract of a definition, of the inductive of a constructor; none for a
    section variable *)
val contract_of : Names.GlobRef.t -> string option

(** What it rests on, by kernel name, through proofs *)
val assumptions_of : Names.GlobRef.t -> string list
