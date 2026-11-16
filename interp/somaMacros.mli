(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Soma: the macros in scope, and how a use of one is expanded. Macros
    are defined in .lang files (vernac/somaMacro.ml, theories/Soma/Macro.v). *)

open Names

(** Is any macro in scope? *)
val any : unit -> bool

(** Is this constant a macro in scope? *)
val is_macro : Constant.t -> bool

(** The library object that makes a constant a macro, in scope where the
    module that defines it is imported *)
val in_macro : Constant.t -> Libobject.obj

(** Is this constant a reader in scope? A reader is defined with
    [Reader name text := body.] in a .lang file: a function from a
    program's text to its top-level forms. *)
val is_reader : Constant.t -> bool

(** The library object that makes a constant a reader, in scope where the
    module that defines it is imported *)
val in_reader : Constant.t -> Libobject.obj

(** [nested ?loc macro f] runs [f], the internalization of an expansion of
    [macro], and fails when expansions are nested too deep: a macro that
    expands to itself does not stop. *)
val nested : ?loc:Loc.t -> Constant.t -> (unit -> 'a) -> 'a

(** [expand env ?loc macro args] is the code that [macro] returns for
    [args], the code of its arguments. Set by vernac/somaMacro.ml. *)
val expand : (Environ.env -> ?loc:Loc.t -> Constant.t ->
              Constrexpr.constr_expr list -> Constrexpr.constr_expr) ref
