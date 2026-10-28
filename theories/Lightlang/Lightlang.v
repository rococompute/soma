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
    after Stdlib (theories/Stdlib), which it uses. The rest of the
    Lightlang library is in the files it exports. *)

Require Export Corelib.Gradual.Gradual.

(** [Succ] is another name for [S], the successor constructor of [nat]. It
    works in patterns too ([Succ m] is any number at least 1, and [m] is one
    less), and terms built with [S] print with [Succ]. *)
Abbreviation Succ := S.

(** Stdlib's binary natural numbers: the type [N], its literals ([5%N], or
    [5] where an [N] is expected) and arithmetic ([+] on [N]s). A [nat] is
    unary, so large [nat]s are slow; [N]s are not. *)
From Stdlib Require Export NArith.

(** Stdlib's [Arith] ([nat] comparisons such as [=?] and [<?], [mod], and
    their lemmas) and [List] ([map], [seq], [filter], [fold_left], ...) *)
From Stdlib Require Export Arith List.

(** Stdlib's [lia] and [nia] tactics, which prove arithmetic facts *)
From Stdlib Require Export Lia.

(** Stdlib's integers [Z], rationals [Q] ([n # d], with [==] for equality
    of fractions), real numbers [R] (with [sqrt]), the bridge [Q2R] from
    rationals to reals, and [lra], [lia] for real numbers *)
From Stdlib Require Export ZArith QArith Reals Qreals Lra.

(** [QArith] opens [Q_scope], which would make [3] a [Q] and [+] the
    addition of [Q]s. Numbers stay [nat]s: rationals are written with
    [%Q], as in [(1 # 2)%Q], and reals with [%R], as in [(sqrt 2)%R]. *)
Close Scope Q_scope.

(** ["..."] string literals, [string] and [append] *)
Require Export Lightlang.Strings.

(** [[1, 2, 3]] list literals *)
Require Export Lightlang.Lists.

(** [to_string] *)
Require Export Lightlang.Show.

(** A type a definition leaves unknown becomes a type parameter, so
    [Definition greet name := append "Hello, " (to_string name).] accepts
    any [name] that has a [to_string]. *)
#[export] Set Automatic Generalization.
