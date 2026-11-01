(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Theorems proved in Lean, [Soma.Lean]

    A Lean file [FILE.lean] proves theorems about Soma's definitions, and
    [FILE.definition], next to it, says what Soma takes them to be:

        Import fib.
        fib_even : forall n, Nat.even (fib (3 * n)) = true.

    [Import FILE.] compiles the definition into a library of the project
    (plugins/soma_lean), where each declared theorem is checked by Lean
    before Soma takes it: Soma translates to Lean the definitions its
    statement uses (a module [Soma], which FILE.lean imports:
    [Soma.fib.fib]), and the statement, which must be the type of
    FILE.lean's theorem of that name. A theorem proved with [sorry] is
    refused. FILE.lean is compiled by the Lean of the project's
    [lean-toolchain], or else elan's default.

    What is translated is a fragment: [nat], [bool], lists, pairs and
    options, their functions and comparisons, the connectives and
    quantifiers, [match], and structural [Fixpoint]s.

    Soma's kernel never sees Lean's proofs: a theorem is an axiom to it,
    trusted as Lean's kernel, the axioms Lean's proof uses, and the
    translation are, which [soma explore] lists. *)

Declare ML Module "soma-runtime.plugins.soma_lean".
