(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * String literals, part of the Lightlang prelude

    ["..."] is a Stdlib [string], a list of ascii characters, everywhere,
    including where an [Any] is expected, so that Stdlib's string functions
    apply to it. Only [string] and [append] are exported: Stdlib's [length]
    or [get] on strings would shadow the ones on lists, and opening
    [string_scope] would make [++] append strings even on lists, so the
    literals get a scope of their own. *)

From Stdlib Require Strings.String.
Export Stdlib.Strings.String(string, append).

Declare Scope lightlang_string_scope.
String Notation string Stdlib.Strings.String.string_of_list_byte
  Stdlib.Strings.String.list_byte_of_string : lightlang_string_scope.
Open Scope lightlang_string_scope.

(** [s ++ t]: the string [s] then [t], where a [string] is expected (the
    argument of a function on strings, or a definition given the type
    [string]); elsewhere [++] appends lists. [(s ++ t)%str] is always on
    strings. *)
Declare Scope lightlang_append_scope.
Delimit Scope lightlang_append_scope with str.
Bind Scope lightlang_append_scope with string.
#[global] Arguments Stdlib.Strings.String.append (_ _)%_str.
Notation "s ++ t" := (append s t) : lightlang_append_scope.
