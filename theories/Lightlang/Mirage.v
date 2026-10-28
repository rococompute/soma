(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * MirageOS unikernels, [Lightlang.Mirage]

    Not part of the prelude. A program that requires it is a unikernel:
    [rocq c prog.light] also builds [prog.hvt], a MirageOS image for
    [solo5-hvt] (Hypervisor.framework on Apple Silicon), whose code is the
    program's [main : io unit] extracted to OCaml (see the [Mirage]
    section of GRADUAL.md).

    [io A] describes what the unikernel does, as data: printing, sleeping,
    looping, in order, ending with a result of type [A]. Building an [io]
    does nothing; the image runs [main]. *)

From Stdlib Require Strings.String.
From Corelib Require Extraction.
(* strings and characters as OCaml char lists and chars in the image *)
From Stdlib Require ExtrOcamlString.

Inductive io : Type -> Type :=
| ret {A : Type} (a : A) : io A
(** [bind m k]: run [m], then [k] on its result *)
| bind {A B : Type} (m : io A) (k : A -> io B) : io B
(** a line on the console *)
| print (s : Stdlib.Strings.String.string) : io unit
| sleep (seconds : nat) : io unit
(** [body], again and again; it never ends, so its type is any [io A] *)
| forever {A : Type} (body : io unit) : io A.

Arguments ret {A} a.
Arguments bind {A B} m k.
Arguments forever {A} body.

Declare Scope io_scope.
Delimit Scope io_scope with io.
Bind Scope io_scope with io.

(** [x <- m ;; rest]: run [m], call its result [x], then [rest].
    [m ;; rest]: run [m], then [rest]. *)
Notation "x <- m ;; rest" := (bind m (fun x => rest))
  (at level 61, m at next level, right associativity) : io_scope.
Notation "m ;; rest" := (bind m (fun _ => rest))
  (at level 61, right associativity) : io_scope.

Open Scope io_scope.
