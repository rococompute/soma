(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The Soma prelude, [Soma.Soma]

    Loaded after [Corelib.Init.Prelude] in every Soma program, unless
    [-no-soma-prelude], [-noinit] or [-boot] is given. It is built
    after Stdlib (theories/Stdlib), which it uses. The rest of the
    Soma library is in the files it exports. *)

Require Export Corelib.Gradual.Gradual.

(** [Rocq Library "rocq-stdpp".]: a Rocq library, which Soma compiles from
    its source, once, and puts in the load path (plugins/soma_rocq) *)
Declare ML Module "soma-runtime.plugins.soma_rocq".

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

(** Stdlib's integers [Z]. Rationals [Q], real numbers [R] (with [sqrt]),
    the bridge [Q2R] from rationals to reals, and [lra] for real numbers
    are opt-in, not in the prelude: a file that wants them imports
    QArith, Reals, Qreals and Lra from Stdlib itself (note [QArith]
    opens [Q_scope], so numbers then need [%Q] / [%R] to stay as written). *)
From Stdlib Require Export ZArith.

(** Boolean operators such as [&&] and [||], in every program. The
    opening is exported, so importing modules inherit it rather than
    having to open bool_scope themselves. *)
Global Open Scope bool_scope.

(** [x != y]: [x] is not equal to [y]. Another spelling of [x <> y], which
    still works; terms print with [!=]. Like [=], it is a proposition, for
    statements and proofs; the [bool] test for code is [negb (x =? y)]. *)
Notation "x != y" := (~ (x = y)) (at level 70, no associativity) : type_scope.

(** ["..."] string literals, [string] and [append] *)
Require Export Soma.Strings.

(** [[1, 2, 3]] list literals *)
Require Export Soma.Lists.

(** [to_string] *)
Require Export Soma.Show.

(** A type a definition leaves unknown becomes a type parameter, so
    [Definition greet name := append "Hello, " (to_string name).] accepts
    any [name] that has a [to_string]. *)
#[export] Set Automatic Generalization.

(** A literal [nat] such as [8080] is computed from its digits instead of
    being written as [8080] [Succ]s; Rocq warns about that every time.
    Numbers like ports and counts are ordinary in programs, so no warning. *)
#[export] Set Warnings "-abstract-large-number".
