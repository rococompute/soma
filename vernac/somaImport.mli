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

(** Is [f] the rules of its folder: X/X.lang, with no X/X.soma? Their
    proofs are in X/X.proof. *)
val is_folder_rules : string -> bool

(** The file being compiled, set by [rocq c] (toplevel/ccompile.ml): what
    a path in it is relative to, when no location says *)
val source_file : string option ref

(** The cache of the project of the file being compiled, ROOT/.soma-cache *)
val project_cache : unit -> string

(** [folder_rules file]: the rules of the folders of the project from its
    root to [file]'s (ROOT/ROOT.lang, X/X.lang, ...), outermost first,
    which apply to every Soma file under them, compiled into the cache when
    they are not up to date; the libraries for [file] to import. *)
val folder_rules : string -> string list
