(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: a project's dependencies: which version of each path a build
    uses, its commit, and its source (see the implementation). *)

type selected = {
  path : string;                 (** github.com/owner/repo *)
  version : SomaProject.version;
  commit : string option;        (** none for a checkout on disk *)
  project : SomaProject.t;       (** its root is the source *)
}

(** What the project's build uses, and all of it on disk: from soma.lock
    when it matches soma.toml, or else resolved, which writes soma.lock.
    Uses the network only for what is not on disk. *)
val ensure : SomaProject.t -> selected list

(** What soma.lock says, for the compilations a build starts, which [ensure]
    has run before *)
val locked : SomaProject.t -> selected list

(** Where the build of the project at [root] compiles this dependency,
    under its .soma-cache *)
val cache_of : root:string -> selected -> string

(** [soma get], in the project above the current folder: [owner/repo@1.2.3]
    or [owner/repo] (its greatest tag) writes that line of [dependencies];
    then, and with no argument, resolves what is written, from the tags
    rather than soma.lock, and writes soma.lock. *)
val get : string option -> unit

(** The project at the tag of that version, fetched if need be *)
val fetched : SomaProject.dependency_path -> SomaProject.version -> SomaProject.t
