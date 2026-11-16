(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Macros, for .ext files

    A .ext file defines macros: [Macro name args := body.] makes [name]
    a function from [args], the code its arguments were written as (a
    [list syntax]), to the code it stands for (a [syntax]). Where the
    macro is in scope, [name a b] is replaced by the code the function
    returns for [a] and [b], which is then checked as if it had been
    written there. A macro is in scope in the .ext file after its
    definition, in FILE.soma and FILE.exp when it is in FILE.ext, and
    in a file that loads its .ext file ([Load "other.ext".]).

    This library is imported in .ext files only, and [Macro] can only be
    used there (vernac/somaMacro.ml). *)

From Soma Require Import Strings.

(** The code a macro is given and returns. Code that is none of the
    others (a notation like [a + b], a [match] whose patterns are not
    names, numbers, strings or constructors applied to names) is
    [Opaque]: a macro cannot look into it, but can return it,
    unchanged. *)
(* [syntax] is nested in [list], for which no [All] scheme is needed *)
#[warnings="-register-all"]
Inductive syntax : Type :=
| Var (name : string)                   (* a name: [x], [Nat.add] *)
| Num (n : nat)                         (* a number: [42] *)
| Str (s : string)                      (* a string: ["abc"] *)
| App (f : syntax) (args : list syntax) (* [f] applied to [args] *)
| Lam (x : string) (body : syntax)      (* [fun x => body] *)
| Hole                                  (* [_] *)
| LetIn (x : string) (value body : syntax) (* [let x := value in body] *)
| Match (scrutinee : syntax) (branches : list (syntax * syntax))
    (* [match scrutinee with p1 => b1 | ... end]: a pattern is a name
       ([x], a constructor [true]), a number, a string, [_], or a
       constructor applied to those ([Succ m], [cons x _]) *)
| Opaque (id : nat)                     (* other code *)
| MacroError (message : string).        (* the expansion fails with [message] *)

Register syntax as soma.macro.syntax.
Register Var as soma.macro.var.
Register Num as soma.macro.num.
Register Str as soma.macro.str.
Register App as soma.macro.app.
Register Lam as soma.macro.lam.
Register Hole as soma.macro.hole.
Register LetIn as soma.macro.letin.
Register Match as soma.macro.match.
Register Opaque as soma.macro.opaque.
Register MacroError as soma.macro.error.

(** * Readers
    A .ext file can also define a reader: [Reader name text := body.]
    makes [name] a function from the text of a program, a [string], to its
    top-level forms, a [list item]. [Read name "text".] in a Soma file,
    or a first line [#lang name] (the rest of the file is the text), runs
    the forms as if they had been written there (vernac/somaMacro.ml). A
    reader sees the text itself, not code Soma has parsed, so it can read
    any syntax: s-expressions, say. *)

(** A top-level form. [pos] is where it starts in the text, a count of
    characters from the start, where an error in it is reported. *)
Inductive item : Type :=
| Def (pos : nat) (name : string) (body : syntax)
    (* [name := body.] *)
| RecDef (pos : nat) (name : string) (params : list string) (body : syntax)
    (* [Recursive name params := body.], checked by Rocq's termination check *)
| Expr (pos : nat) (term : syntax)
    (* [term.], evaluated, as a bare term is *)
| ReadError (pos : nat) (message : string).
    (* reading fails with [message], at [pos] *)

Register item as soma.reader.item.
Register Def as soma.reader.def.
Register RecDef as soma.reader.recdef.
Register Expr as soma.reader.expr.
Register ReadError as soma.reader.error.

(** A string as the codes of its characters, and back: a reader can walk
    its text as a [list nat], with no library of characters *)
Fixpoint chars (s : string) : list nat :=
  match s with
  | String.EmptyString => nil
  | String.String c rest => cons (Ascii.nat_of_ascii c) (chars rest)
  end.

Fixpoint of_chars (codes : list nat) : string :=
  match codes with
  | nil => String.EmptyString
  | cons n rest => String.String (Ascii.ascii_of_nat n) (of_chars rest)
  end.
