(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: a project's soma.toml, which says what the project is, and marks
    its root: the folder its imports and its .soma-cache are in. *)

(** "soma.toml" *)
val file_name : string

(** A semantic version (https://semver.org): MAJOR.MINOR.PATCH, then
    -PRERELEASE and +BUILD, each a list of dot-separated identifiers *)
type version = {
  major : int;
  minor : int;
  patch : int;
  pre : string list;
  build : string list;
}

val version_to_string : version -> string

(** [Error why], [why] being what a version is not *)
val parse_version : string -> (version, string) result

type t = {
  root : string;                 (** the folder of soma.toml, canonical *)
  name : string;                 (** lowercase letters, digits and _, beginning with a letter *)
  description : string option;
  version : version;
}

(** The folder of the nearest soma.toml, from [dir] up *)
val find_root : string -> string option

(** The project whose root is [root], from its soma.toml, checked: a user
    error, saying what to write, when it is wrong *)
val load : string -> t

(** The project of [file] (a file of it, or a folder), if it has a soma.toml *)
val of_file : string -> t option
