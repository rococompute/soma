(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacexpr

(* Interpretation of search commands *)

val interp_search_request :
  Environ.env ->
  Evd.evar_map ->
  bool * Vernacexpr.search_request ->
  bool * Search.glob_search_request

val interp_search_restriction : Libnames.qualid list search_restriction -> Libnames.full_path list search_restriction

val interp_search : Environ.env -> Evd.evar_map ->
  searchable -> Libnames.qualid list search_restriction -> unit

(** What a search finds, given to [display], and not printed *)
val run_search : Environ.env -> Evd.evar_map -> Vernacexpr.searchable ->
  Libnames.qualid list Vernacexpr.search_restriction -> Search.display_function -> unit

(** The pattern of a search for one pattern *)
val search_pattern : Environ.env -> Evd.evar_map -> Vernacexpr.searchable -> Pattern.constr_pattern option
