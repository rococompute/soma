(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: TOML 1.0 (https://toml.io/en/v1.0.0), which soma.toml is
    written in. Dates and times are refused. *)

type value =
  | String of string
  | Int of int
  | Float of float
  | Bool of bool
  | Array of value list
  | Table of table

(** A table's keys, in the order of the file, each with the line it is
    defined on *)
and table = (string * entry) list

and entry = { line : int; value : value }

(** The line, and what is wrong *)
exception Error of int * string

val parse : string -> table

(** "a string", "an integer", ...: for messages *)
val describe : value -> string
