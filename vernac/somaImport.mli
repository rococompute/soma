(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: [Import] compiles what it imports, in Soma files (see the
    implementation). *)

(** Is the command at [loc] in a Soma file (.soma, .proof, .lang)? *)
val applies : ?loc:Loc.t -> unit -> bool

(** [prepare ?loc qids], for an [Import] of names that are no modules in
    scope: those that are files of the program's project are compiled into
    its .soma-cache when they are not up to date, and the cache is put in
    the load path. Whether any is such a file. *)
val prepare : ?loc:Loc.t -> Libnames.qualid list -> bool

(** Written at the end of a compilation that [prepare] started: its stamp,
    the hash of its source and the digests of what it imported *)
val write_stamp : unit -> unit
