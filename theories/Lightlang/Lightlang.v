(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The Lightlang prelude, [Lightlang.Lightlang]

    Loaded after [Corelib.Init.Prelude] in every Lightlang program, unless
    [-no-lightlang-prelude], [-noinit] or [-boot] is given. It is built
    after Stdlib (theories/Stdlib), which it uses. *)

Require Export Corelib.Gradual.Gradual.

(** String literals: ["..."] is a Stdlib [string], a list of ascii
    characters, everywhere, including where an [Any] is expected, so that
    Stdlib's string functions apply to it. Only [string] and [append] are
    exported: Stdlib's [length] or [get] on strings would shadow the ones
    on lists, and opening [string_scope] would make [++] append strings
    even on lists, so the literals get a scope of their own. *)
From Stdlib Require Strings.String.
Export Stdlib.Strings.String(string, append).

Declare Scope lightlang_string_scope.
String Notation string Stdlib.Strings.String.string_of_list_byte
  Stdlib.Strings.String.list_byte_of_string : lightlang_string_scope.
Open Scope lightlang_string_scope.
