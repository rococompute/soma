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

(** Semantic version precedence: a release is greater than its pre-release *)
val compare_version : version -> version -> int

(** Where a dependency is fetched from: [owner/repo], [host.com/group/repo],
    [git@host.com:group/repo.git], or [ssh://git@host.com/group/repo.git],
    each with [/vN] for major 2 and above. SSH and HTTPS share an identity. *)
type dependency_path = {
  canonical : string;            (** github.com/owner/repo/v2 *)
  url : string;                  (** The HTTPS or SSH Git transport. *)
  major : int option;            (** N, of the suffix /vN *)
}

(** [Error why], [why] being the message for the key *)
val parse_path : string -> (dependency_path, string) result

(** Split a final [@VERSION] from a dependency path, preserving SSH's
    [user@host]. A missing version is [None]. *)
val split_version : string -> string * string option

(** A version as the value of a dependency at this path: not build metadata,
    and its major that of the path. [Error why], the message. *)
val check_dependency_version : written:string -> dependency_path -> version -> (unit, string) result

type dependency_source =
  | Version of version
  | Checkout of string           (** a folder with a soma.toml, canonical *)

type dependency = {
  written : string;              (** the key, as soma.toml has it *)
  path : dependency_path;
  source : dependency_source;
  line : int;
}

(** its [image] table: how a MirageOS image of the project is built *)
type user_memory = { name : string; address : int option; size : int }

type image = {
  memory : int option;      (** megabytes, which soma run gives the image (256 by default) *)
  text_start : int option;  (** the address the image's code is linked at (solo5's 0x100000
                                by default), a multiple of 0x10000 below [memory] *)
  user_memory : user_memory list; (** hvt memory reserved for loaded guest programs *)
}

val no_image : image

type mirage_device = Block_file of string | Default_network

type mirage = {
  job_name : string;
  main_module : string;
  packages : string list;
  local_libs : string list;
  devices : mirage_device list;
}

type t = {
  root : string;                 (** the folder of soma.toml, canonical *)
  name : string;                 (** lowercase letters, digits and _, beginning with a letter *)
  description : string option;
  version : version;
  dependencies : dependency list; (** its [dependencies] table *)
  opam : (string * string) list;  (** its [opam] table: opam packages, each at its version *)
  image : image;
  mirage : mirage option;
  build : SomaBuildPlan.t option;
}

(** The folder of the nearest soma.toml, from [dir] up *)
val find_root : string -> string option

(** The project whose root is [root], from its soma.toml, checked: a user
    error, saying what to write, when it is wrong. Its errors name the file
    as [display]: "soma.toml" of a fetched project, with its path. *)
val load : ?display:string -> string -> t

(** [load], after soma.toml was rewritten *)
val reload : string -> t

(** The project of [file] (a file of it, or a folder), if it has a soma.toml *)
val of_file : string -> t option
