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

(** Is the command at [loc] in a Soma file (.soma, .exp, .ext)? *)
val applies : ?loc:Loc.t -> unit -> bool

(** [prepare ?loc qids], for an [Import] of names that are no modules in
    scope: those that are files of the program's project, or of a dependency
    it names, are compiled into its .soma-cache when they are not up to date,
    and the cache is put in the load path. The names to require, in order:
    those of their libraries. *)
val prepare : ?loc:Loc.t -> Libnames.qualid list -> Libnames.qualid list

(** An error when a [Require] ([from], [qids]) names a dependency of a dependency,
    which this project's soma.toml does not name *)
val refuse_undeclared_require : ?loc:Loc.t -> Libnames.qualid option -> Libnames.qualid list -> unit

(** The same, for an [Import] of [qid], a module in scope, resolved to that module *)
val refuse_undeclared_module : ?loc:Loc.t -> Libnames.qualid -> Names.ModPath.t -> unit

(** Does [qid], a file of this project, resolve to [mp], a library of the
    same last name that is not it? *)
val names_another_library : ?loc:Loc.t -> Libnames.qualid -> Names.ModPath.t -> bool

(** For what imports a file that named a Rocq library: that library's
    logical name and folder, kept in the build's cache *)
val record_load_path : string -> string -> unit

(** The variable a compilation is a dependency's by, which is set to its name *)
val prefix_var : string

(** An error, in a compilation of a dependency, saying that [command] [does]
    ("writes a file") and works when the project is built on its own; in any
    other compilation, nothing. *)
val refuse_in_dependency : ?does:string -> string -> unit

(** The variable a compilation of a Rocq library (plugins/soma_rocq) is by,
    which is set to the library's name *)
val rocq_library_var : string

(** An error, for a [Declare ML Module] in a compilation of a Rocq
    library; in any other compilation, nothing. *)
val refuse_ml_module_in_rocq_library : unit -> unit

(** Written at the end of a compilation that [prepare] started: its stamp,
    the hash of its source and the digests of what it imported *)
val write_stamp : unit -> unit

(** Is [f] the rules of its folder: X/X.ext, with no X/X.soma? Their
    proofs are in X/X.exp. *)
val is_folder_rules : string -> bool

(** [refuse_old_names base] fails when [base.lang] or [base.proof] exists:
    they are [base.ext] and [base.exp] now, and one left with its old name
    would not be read. *)
val refuse_old_names : string -> unit

(** The file being compiled, set by [rocq c] (toplevel/ccompile.ml): what
    a path in it is relative to, when no location says *)
val source_file : string option ref

(** Set only while Soma loads the extraction commands it generates itself
    (toplevel/somaOcaml.ml, toplevel/somaMirage.ml): their [Extraction "prog"]
    goes to the output directory they set, outside the S-5 project check that
    explicit Extraction and Redirect targets get. No Soma command sets it. *)
val generated_output : bool ref

(** The cache of the project being built, ROOT/.soma-cache *)
val project_cache : unit -> string

(** [project_file f]: how a compiled library records [f], a file of the
    project being compiled (FILE.ml beside its FILE.definition): relative to
    the project's root, or absolute when it is a dependency's or outside
    the project. *)
val project_file : string -> string

(** [resolve_project_file f]: the file that [f], as [project_file] gave it,
    is in the project being built: a relative [f] is under that project's
    root, so a .vo compiled in another checkout names this one's file. *)
val resolve_project_file : string -> string

(** [folder_rules file]: the rules of the folders of the project from its
    root to [file]'s (ROOT/ROOT.ext, X/X.ext, ...), outermost first,
    which apply to every Soma file under them, compiled into the cache when
    they are not up to date; the libraries for [file] to import. *)
val folder_rules : string -> string list

(** Record the compiled interface after a successful compilation. *)
val record_interface : source:string -> dirpath:Names.DirPath.t -> vo_file:string -> unit

(** Write the requested test entry point's complete project import trace,
    after imported proof checks have finished. *)
val record_test_dependencies : source:string -> unit

(** Proofs checked beside the build: a file with a .exp is compiled first
    without its proofs, for its importers, and its proofs are checked by a
    compilation of their own, at the same time as the rest of the build. *)

(** Made by the compilation that starts a build, for the compilations it starts *)
val start_proof_jobs : unit -> unit

(** Waits for the build's proof checks, and fails if one failed *)
val wait_proof_jobs : unit -> unit

(** A compilation without the proofs of its lemmas, for its importers *)
val is_interface : unit -> bool

(** In a proof check: waits for a slot; the function says it succeeded *)
val acquire_proof_slot : unit -> (unit -> unit)

(** Where a compilation writes its .vo [vo], and puts it in place *)
val checked_output : string -> string
val install_checked : vo:string -> unit
