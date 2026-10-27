(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The Lightlang prelude, [Corelib.Lightlang.Lightlang]

    Loaded after [Corelib.Init.Prelude] in every Lightlang program, unless
    [-no-lightlang-prelude], [-noinit] or [-boot] is given. *)

Require Export Corelib.Gradual.Gradual.

(** String literals: ["..."] is a primitive [string] everywhere, including
    where a [Dyn] is expected. Only [string] and [cat] are exported, since
    [PrimString.length] would shadow the length of lists. *)
Require Corelib.Strings.PrimString.
Export Corelib.Strings.PrimString(string, cat).
Export Corelib.Strings.PrimString.PStringNotations.
Open Scope pstring_scope.
