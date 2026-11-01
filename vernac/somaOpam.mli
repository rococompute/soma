(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: what it takes from opam, for the OCaml modules a program uses
    (toplevel/somaOcaml.ml) and the Rocq libraries it names
    (plugins/soma_rocq). *)

(** [$XDG_CACHE_HOME/soma], or [~/.cache/soma] *)
val cache_root : unit -> string

(** The opam switch: [$SOMA_OCAML_SWITCH], or the one Soma makes in
    [cache_root ()/ocaml] (then [true]: it is Soma's) *)
val switch : unit -> string * bool

(** [switch ()], made if it is Soma's and does not exist yet, saying so on
    stderr with [who] ("OCaml", "Rocq"); [log] has opam's output. Fails,
    saying how to install it, when opam is not installed. *)
val ensure_switch : who:string -> log:string -> string

(** [args] run, their output in [log]: whether they succeeded *)
val run : log:string -> string list -> bool

val command_exists : string -> bool

(** the lines of a file that are not empty, or none *)
val read_lines : string -> string list

(** the last [lines] lines of a file *)
val tail_of_file : ?lines:int -> string -> string

val mkdir_p : string -> unit
