(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * WebAssembly modules, [Soma.Wasm]

    A module [FILE.wasm] is used from Soma through [FILE.definition], next
    to it, which says what Soma takes its exports to be:

        add : N -> N -> N.
        checksum : Any -> Any.

    [Import FILE.] compiles the two into a library of the project, where
    each declared name is the module's export of that name, checked when
    it is compiled: it exists, takes as many arguments, and its numbers
    fit the declared types (plugins/soma_wasm). A declared type is [N],
    [Z], [Any], or the module's own [i64] or [i32]: a value of the module
    that it cannot hold ([-5] for an [N]) fails as a cast does, with what
    the module gave ("expected an N, but got I64 (-5) : i64"), and so does
    an argument that the module cannot take, and a trap.

    The calls are computed when Soma evaluates a term (a bare term,
    Explore), by the WebAssembly reference interpreter, and never by the
    kernel: the exports are parameters to it, so that no proof computes
    through a module. *)

From Corelib Require Import BinNums.
From Stdlib Require Strings.String.
Require Import Soma.Strings.

(** the module's numbers, as Soma sees them when they do not fit *)
Inductive i64 : Type := I64 (value : Z).
Inductive i32 : Type := I32 (value : Z).

(** a module that stopped ("unreachable", "integer divide by zero") *)
Inductive trap : Type := Trapped (message : string).

Declare ML Module "soma-runtime.plugins.soma_wasm".
